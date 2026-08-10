import FormalConjectures.Util.ProblemImports

theorem helper0 (n : ℕ) (h_low : 4 ≤ n) (hn : n ≤ 1003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 2, 2; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 11; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 13; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 13; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 17; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 19; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 19; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 23; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 23; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 23; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 29; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 31; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 31; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 31; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 37; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 37; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 41; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 43; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 43; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 47; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 47; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 47; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 53; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 53; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 53; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 59; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 61; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 61; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 61; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 67; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 67; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 71; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 73; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 73; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 73; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 79; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 79; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 83; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 83; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 83; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 89; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 89; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 89; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 79; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 97; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 97; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 107; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 149; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 191; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 223; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 223; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 227; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 239; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 241; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 241; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 241; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 239; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 241; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 263; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 263; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 263; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 269; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 353; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 353; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 353; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 383; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 383; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 383; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 401; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 401; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 401; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 401; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 431; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 439; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 439; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 443; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 443; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 443; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 439; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 461; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 487; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 487; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 487; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 509; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 509; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 509; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 509; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 509; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 509; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 587; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 587; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 587; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 601; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 601; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 601; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 641; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 773; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 773; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 773; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 773; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 773; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 773; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 809; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 809; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 821; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 859; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 859; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 859; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 859; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 929; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 929; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 929; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 941; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 941; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 941; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 977; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 977; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 977; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 73, 919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 991; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 991; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 991; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper1 (n : ℕ) (h_low : 1004 ≤ n) (hn : n ≤ 2003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 7, 997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1009; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1009; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1031; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1033; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1033; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1033; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1031; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1061; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1063; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1063; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1063; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1061; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1061; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1093; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1093; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1097; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1097; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1097; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1117; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1117; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1117; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1123; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1123; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1123; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 1109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 1103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 1109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1223; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1223; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1223; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1249; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1249; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1249; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 1229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1249; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1249; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 1237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1279; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1279; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1291; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1291; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1291; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1303; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1303; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1303; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 1319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 1307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 1319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 1321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 1321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 1367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 1381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1429; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1429; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1439; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1439; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1439; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1429; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1453; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1453; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1453; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 1451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1487; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 1489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1543; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1543; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1543; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1597; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1597; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1601; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1601; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1601; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1609; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1609; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1627; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1627; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1627; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1627; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1627; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1627; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1667; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1667; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1667; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1667; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1697; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1697; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1721; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1721; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1747; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1747; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1747; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 1721; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 1733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1811; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 67, 1789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 1831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1873; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1873; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1901; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1901; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1901; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 1879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 1867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1913; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1979; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1979; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1979; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 1951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 1987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 1993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 1999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper2 (n : ℕ) (h_low : 2004 ≤ n) (hn : n ≤ 3003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 5, 1999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 1999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2017; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2017; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2017; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2017; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 2017; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2063; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2063; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2063; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 2017; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2081; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2083; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2083; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2141; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2141; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 2141; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 2153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 2161; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2207; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2207; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2207; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2239; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2239; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2239; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2267; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2269; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2269; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2269; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2293; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2339; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2341; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2341; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2341; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2341; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2371; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2371; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2371; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2377; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2377; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2383; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2383; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2383; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 2389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 2377; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2437; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2437; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2437; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2437; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 2473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 2459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 2477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2539; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2539; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2543; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2543; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2543; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2551; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2551; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2551; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 2549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2579; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2609; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2609; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2609; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 2557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2633; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2633; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2633; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 103, 2539; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2633; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2633; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2633; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2671; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2671; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2671; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2687; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2707; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2707; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2711; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2713; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2713; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2713; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2711; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2731; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2731; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2731; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2731; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2731; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2777; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2819; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2819; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2819; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2819; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2819; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2837; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2837; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2837; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2843; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2843; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2843; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2897; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2897; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2897; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2887; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 2917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 2953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 2969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 2971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 2999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper3 (n : ℕ) (h_low : 3004 ≤ n) (hn : n ≤ 4003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 3, 3001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 2999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3041; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3041; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3041; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3041; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3061; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3061; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3061; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 3023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3083; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3083; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3083; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3137; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 3121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3169; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3169; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3169; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3169; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3169; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3181; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3191; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3191; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3191; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3191; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3191; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3251; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3299; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3313; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3319; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3329; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3329; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3371; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3371; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3371; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 67, 3391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3461; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3511; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 3467; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3533; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3533; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3533; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3539; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3539; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3593; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3613; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3631; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3617; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3671; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3677; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3697; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3697; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3697; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 3701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3767; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 3733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3797; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 79, 3739; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3821; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3821; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 79, 3769; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3847; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3929; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3929; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 3931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 3929; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 3947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 3989; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 3989; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 3989; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 3967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 3989; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 3989; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper4 (n : ℕ) (h_low : 4004 ≤ n) (hn : n ≤ 5003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 3, 4001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4049; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4073; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4073; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4073; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4093; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4093; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4093; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 4079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 4111; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 4139; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 4157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 4159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 4157; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4201; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4241; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4241; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4259; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 4261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 4261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 4283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 4289; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4327; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4339; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4339; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4339; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4339; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4339; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4363; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4363; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4363; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4363; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4363; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4391; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 4363; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 4357; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4409; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4423; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4463; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4493; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 4447; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4513; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4513; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4519; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4519; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4519; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4519; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4513; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4519; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 4523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4567; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4597; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4597; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4597; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 71, 4547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 4583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 4583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4651; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4651; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4651; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 4663; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 4651; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 4657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4721; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4729; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4751; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 4723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4787; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4799; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4799; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 4799; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 4813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 4831; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 4817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 73, 4813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 4861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 4861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 4889; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4909; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4931; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 4943; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4957; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 4973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 4973; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 4969; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 4993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 4993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 4999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper5 (n : ℕ) (h_low : 5004 ≤ n) (hn : n ≤ 6003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 5, 4999; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5003; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5009; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5009; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5021; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5023; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5051; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5059; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5077; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5077; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5081; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5081; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5081; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5077; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5107; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5107; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5107; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 5087; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 5099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 5099; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5147; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5147; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5147; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 5119; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5153; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 5107; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5167; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5189; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5189; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5189; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5179; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5189; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5189; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 5171; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5209; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5227; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5227; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5231; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5227; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5261; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5273; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5279; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5279; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5279; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5303; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5303; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5303; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 67, 5281; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 139, 5233; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5381; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5387; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5387; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5387; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5399; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 5347; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5407; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5413; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5419; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5431; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5431; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5431; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5437; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5437; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5443; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5443; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5443; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5441; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5471; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5479; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5483; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5501; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5503; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5519; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5531; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5527; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5557; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 5573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 5581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 5591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5623; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5641; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5641; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5641; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5647; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5651; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5657; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5683; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5693; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5711; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5711; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5711; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5743; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 5717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5749; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5783; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5801; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5807; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5807; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5807; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5821; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5821; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5821; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5813; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5839; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5843; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5843; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5843; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5849; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5851; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5861; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5897; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5897; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5897; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5903; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 67, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 5923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 5927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 97, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 5939; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5981; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5981; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5981; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 5953; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 79, 5923; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper6 (n : ℕ) (h_low : 6004 ≤ n) (hn : n ≤ 7003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 17, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 5987; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 127, 5881; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6011; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6029; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6007; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6047; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6047; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6047; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6053; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6037; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6067; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6073; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6073; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6073; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 6047; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6089; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6101; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6091; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6113; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6131; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6133; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6143; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6163; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6173; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 6151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6197; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6199; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6217; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6221; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 6203; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6257; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6263; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6263; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6263; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6269; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6271; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6269; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6277; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6287; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6299; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6299; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6311; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6317; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6323; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6329; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6329; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6329; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6301; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6337; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6329; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6343; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6353; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6353; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6353; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6361; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6367; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6373; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6359; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6397; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 6379; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6421; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 6389; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6427; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6449; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 6473; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6491; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 6469; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6521; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6551; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6551; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6553; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6563; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6569; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6571; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 6581; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6619; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 6599; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6637; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6653; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6661; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6659; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6679; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6689; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6701; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6709; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6719; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 67, 6691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6737; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6733; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6763; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6763; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6763; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6763; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6763; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6761; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6763; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6781; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6781; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6781; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6779; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6781; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6791; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6781; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6803; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6827; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6833; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6857; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6863; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6869; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6899; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6899; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6899; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 6871; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6911; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 6907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6917; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6947; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 6949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6959; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6961; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6961; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6961; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6967; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6971; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6977; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6977; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6977; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6983; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6961; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6991; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6991; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 6991; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 6997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 6997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega


theorem helper7 (n : ℕ) (h_low : 7004 ≤ n) (hn : n ≤ 8003) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  interval_cases n
  · use 3, 7001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 6997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7001; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7013; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 6997; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7027; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7039; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7043; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 7019; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7069; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7079; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7103; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 7057; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7109; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7121; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7129; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7151; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 7127; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7187; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 7159; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7193; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7177; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7207; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7207; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7213; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7211; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7229; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7247; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 7243; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 73, 7219; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 7237; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7283; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7297; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7309; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7307; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7321; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7333; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 7331; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7369; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 7351; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 59, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7393; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 173, 7253; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 83, 7349; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7411; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7417; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7433; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7451; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7457; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7459; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7477; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7481; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7487; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7487; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7489; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7499; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7517; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7523; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7529; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7507; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7537; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7537; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7541; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7547; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7549; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7559; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7561; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7573; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7577; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7583; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7589; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7589; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7591; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7603; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7607; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7643; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 43, 7621; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7649; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7639; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7673; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7669; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7681; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7681; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7681; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7687; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7687; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7691; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7687; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7703; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7699; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7717; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7723; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7727; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7741; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7757; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 7753; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7793; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7817; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7823; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 79, 7759; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7829; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7841; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 73, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7853; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 79, 7789; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7873; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7873; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7877; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7883; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7901; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7901; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7901; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 7879; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7907; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7919; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 61, 7867; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7927; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7933; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 11, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 13, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 17, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 19, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 47, 7937; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 23, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 37, 7951; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 41, 7949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 29, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 31, 7963; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 3, 7993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 5, 7993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 7, 7993; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega
  · use 53, 7949; refine ⟨by norm_num, by norm_num, rfl⟩
  · rcases he with ⟨k, hk⟩; omega

