import FormalConjecturesUtil

/-!
An auxiliary test of a digit construction, not a settlement of Erdős 773.
The definitions below track rational rotations through affine digit words.
-/
namespace Erdos773.ParametricSphere

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

structure Step where
  constant : Fin 4 → ℕ
  slope : Fin 4 → ℕ
  next : ℤ × ℤ

def base (t : ℕ) : ℕ := 256 + 124160 * t

def digit (s : Step) (j : Fin 4) (t : ℕ) : ℕ :=
  2 * s.constant j + 256 * s.slope j * t

def value (ss : List Step) (j : Fin 4) (t : ℕ) : ℕ :=
  ss.foldr (fun s n => digit s j t + base t * n) 1

def ivalue (ss : List Step) (j : Fin 4) (t : ℕ) : ℤ :=
  ss.foldr (fun s n =>
    2 * (s.constant j : ℤ) + 256 * (s.slope j : ℤ) * t + (256 + 124160 * (t : ℤ)) * n) 1

lemma cast_value (ss : List Step) (j : Fin 4) (t : ℕ) :
    (value ss j t : ℤ) = ivalue ss j t := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [value, ivalue, List.foldr_cons, digit, base, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] at ih ⊢
    rw [ih]

def checkStep (s : Step) (k l : ℤ) : Bool := decide (
  485 * (s.constant 2 : ℤ) = 476 * s.constant 0 + 93 * s.constant 1 - k + 256 * s.next.1 ∧
  485 * (s.constant 3 : ℤ) = -93 * s.constant 0 + 476 * s.constant 1 - l + 256 * s.next.2 ∧
  485 * (s.slope 2 : ℤ) = 476 * s.slope 0 + 93 * s.slope 1 + 970 * s.next.1 ∧
  485 * (s.slope 3 : ℤ) = -93 * s.slope 0 + 476 * s.slope 1 + 970 * s.next.2)

def checkPath : List Step → ℤ → ℤ → Bool
  | [], k, l => decide (k = 42 ∧ l = -51)
  | s :: ss, k, l => checkStep s k l && checkPath ss s.next.1 s.next.2

lemma rotation_of_checkPath (ss : List Step) (t : ℕ) (k l : ℤ)
    (h : checkPath ss k l = true) :
    485 * ivalue ss 2 t - 476 * ivalue ss 0 t - 93 * ivalue ss 1 t = -2 * k ∧
    485 * ivalue ss 3 t + 93 * ivalue ss 0 t - 476 * ivalue ss 1 t = -2 * l := by
  induction ss generalizing k l with
  | nil =>
    have hk : k = 42 ∧ l = -51 := of_decide_eq_true h
    rcases hk with ⟨rfl, rfl⟩
    norm_num [ivalue]
  | cons s ss ih =>
    have hh : checkStep s k l = true ∧ checkPath ss s.next.1 s.next.2 = true := by
      simpa only [checkPath, Bool.and_eq_true_iff] using h
    obtain ⟨hs, ht⟩ := hh
    have hs' := of_decide_eq_true hs
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hs'
    obtain ⟨hi₁, hi₂⟩ := ih _ _ ht
    simp only [ivalue, List.foldr_cons] at hi₁ hi₂ ⊢
    constructor
    · linear_combination 2 * h₁ + 256 * (t : ℤ) * h₃ +
        (256 + 124160 * (t : ℤ)) * hi₁
    · linear_combination 2 * h₂ + 256 * (t : ℤ) * h₄ +
        (256 + 124160 * (t : ℤ)) * hi₂

lemma norm_collision_of_checkPath (ss : List Step)
    (h : checkPath ss 0 0 = true) (t : ℕ) :
    value ss 0 t ^ 2 + value ss 1 t ^ 2 = value ss 2 t ^ 2 + value ss 3 t ^ 2 := by
  have hi := rotation_of_checkPath ss t 0 0 h
  have h₁ : 485 * ivalue ss 2 t = 476 * ivalue ss 0 t + 93 * ivalue ss 1 t := by
    linarith [hi.1]
  have h₂ : 485 * ivalue ss 3 t = -93 * ivalue ss 0 t + 476 * ivalue ss 1 t := by
    linarith [hi.2]
  have hsq₁ := congrArg (fun x : ℤ => x ^ 2) h₁
  have hsq₂ := congrArg (fun x : ℤ => x ^ 2) h₂
  have he : ivalue ss 0 t ^ 2 + ivalue ss 1 t ^ 2 =
      ivalue ss 2 t ^ 2 + ivalue ss 3 t ^ 2 := by nlinarith only [hsq₁, hsq₂]
  simp only [← cast_value] at he
  exact_mod_cast he

lemma sum_digits (ss : List Step) (j : Fin 4) (t : ℕ) :
    (ss.map (fun s => digit s j t)).sum =
      2 * (ss.map (fun s => s.constant j)).sum +
        256 * t * (ss.map (fun s => s.slope j)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [digit]
    ring

lemma sum_square_digits (ss : List Step) (j : Fin 4) (t : ℕ) :
    (ss.map (fun s => digit s j t ^ 2)).sum =
      4 * (ss.map (fun s => s.constant j ^ 2)).sum +
        1024 * t * (ss.map (fun s => s.constant j * s.slope j)).sum +
        65536 * t ^ 2 * (ss.map (fun s => s.slope j ^ 2)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [digit]
    ring



-- A shared dictionary keeps the explicit finite certificate compact.
def mkStep (a b c d u v w z : ℕ) (k l : ℤ) : Step :=
  ⟨![a, b, c, d], ![u, v, w, z], (k, l)⟩

def step0 : Step := mkStep 1 45 17 35 47 161 105 115 14 (-17)
def step1 : Step := mkStep 60 48 10 33 205 145 9 93 (-110) (-5)
def step2 : Step := mkStep 63 19 5 62 228 69 7 234 (-115) 105
def step3 : Step := mkStep 58 6 5 41 200 35 1 172 (-101) 88
def step4 : Step := mkStep 56 61 22 12 165 235 37 59 (-85) (-70)
def step5 : Step := mkStep 28 58 43 10 58 209 113 36 8 (-79)
def step6 : Step := mkStep 40 28 52 11 13 189 77 149 14 (-17)
def step7 : Step := mkStep 59 24 6 26 211 83 9 93 (-107) 26
def step8 : Step := mkStep 60 27 2 54 222 131 7 234 (-118) 74
def step9 : Step := mkStep 59 32 2 59 222 131 7 234 (-118) 74
def step10 : Step := mkStep 47 2 4 63 203 4 38 231 (-81) 133
def step11 : Step := mkStep 62 5 34 45 107 26 4 203 (-53) 99
def step12 : Step := mkStep 4 15 56 9 11 48 206 27 93 (-9)
def step13 : Step := mkStep 59 56 3 50 230 210 18 186 (-124) 12
def step14 : Step := mkStep 34 26 46 10 61 178 122 129 14 (-17)
def step15 : Step := mkStep 58 52 22 3 216 193 79 8 (-85) (-70)
def step16 : Step := mkStep 58 21 15 47 214 52 46 152 (-87) 71
def step17 : Step := mkStep 63 24 55 62 169 32 128 191 (-22) 96
def step18 : Step := mkStep 62 0 6 18 205 145 21 217 (-104) 57
def step19 : Step := mkStep 62 52 4 29 236 148 6 62 (-127) (-19)
def step20 : Step := mkStep 21 56 39 42 55 240 128 191 14 (-17)
def step21 : Step := mkStep 16 60 39 5 10 220 96 22 22 (-96)
def step22 : Step := mkStep 34 38 48 22 87 71 127 19 14 (-17)
def step23 : Step := mkStep 57 58 0 36 230 210 12 124 (-127) (-19)
def step24 : Step := mkStep 55 62 12 6 227 241 65 25 (-102) (-84)
def step25 : Step := mkStep 36 16 46 0 84 102 130 50 14 (-17)
def step26 : Step := mkStep 54 19 45 59 200 35 159 188 (-22) 96
def step27 : Step := mkStep 56 63 15 23 174 142 0 0 (-99) (-53)
def step28 : Step := mkStep 15 14 25 2 42 51 79 8 14 (-17)
def step29 : Step := mkStep 4 54 62 31 36 113 237 24 90 (-40)
def step30 : Step := mkStep 61 24 2 51 222 131 7 234 (-118) 74
def step31 : Step := mkStep 48 9 30 59 93 9 21 217 (-36) 113
def step32 : Step := mkStep 29 23 15 2 196 238 170 140 (-34) (-28)
def step33 : Step := mkStep 63 2 0 29 242 86 18 186 (-118) 74
def step34 : Step := mkStep 41 48 57 30 13 189 77 149 14 (-17)
def step35 : Step := mkStep 39 34 52 17 132 91 175 30 14 (-17)
def step36 : Step := mkStep 32 12 10 16 217 21 127 19 (-45) 20
def step37 : Step := mkStep 51 1 6 45 169 32 4 203 (-84) 102
def step38 : Step := mkStep 57 12 60 17 112 136 142 174 3 31
def step39 : Step := mkStep 63 15 4 58 231 38 4 203 (-115) 105
def step40 : Step := mkStep 55 3 3 55 203 4 4 203 (-98) 119
def step41 : Step := mkStep 21 14 52 48 25 65 145 205 54 73
def step42 : Step := mkStep 29 17 39 2 5 110 54 73 14 (-17)
def step43 : Step := mkStep 20 51 37 37 143 139 195 75 14 (-17)
def step44 : Step := mkStep 21 6 16 27 194 97 187 154 (-11) 48
def step45 : Step := mkStep 48 39 62 20 39 82 82 39 14 (-17)
def step46 : Step := mkStep 44 34 17 28 152 46 34 28 (-62) 6
def step47 : Step := mkStep 33 37 47 21 55 240 128 191 14 (-17)
def step48 : Step := mkStep 54 7 1 43 197 66 4 203 (-101) 88
def step49 : Step := mkStep 8 21 30 34 13 189 117 239 34 28
def step50 : Step := mkStep 26 53 43 38 87 71 127 19 14 (-17)
def step51 : Step := mkStep 55 6 11 49 197 66 38 231 (-84) 102
def step52 : Step := mkStep 45 46 59 11 33 144 82 39 11 (-48)
def step53 : Step := mkStep 33 43 48 27 70 85 113 36 14 (-17)
def step54 : Step := mkStep 50 45 7 23 213 224 60 135 (-96) (-22)
def step55 : Step := mkStep 29 29 49 5 75 195 167 109 28 (-34)
def step56 : Step := mkStep 61 10 10 61 203 4 4 203 (-98) 119
def step57 : Step := mkStep 13 3 27 57 14 17 69 228 26 107
def step58 : Step := mkStep 62 5 19 63 203 4 38 231 (-81) 133
def step59 : Step := mkStep 23 8 57 0 90 40 220 10 62 (-6)
def step60 : Step := mkStep 2 62 0 4 55 240 48 11 (-26) (-107)
def step61 : Step := mkStep 15 20 26 8 132 91 175 30 14 (-17)
def step62 : Step := mkStep 49 21 3 16 188 159 29 138 (-93) 9
def step63 : Step := mkStep 35 46 27 40 134 232 114 208 (-31) 3
def step64 : Step := mkStep 27 23 22 10 227 241 235 165 (-17) (-14)
def step65 : Step := mkStep 63 20 5 63 228 69 7 234 (-115) 105
def step66 : Step := mkStep 42 4 29 30 107 26 60 135 (-25) 65
def step67 : Step := mkStep 49 21 30 38 95 150 38 231 (-42) 51
def step68 : Step := mkStep 61 2 16 44 169 32 4 203 (-84) 102
def step69 : Step := mkStep 5 63 54 16 13 189 189 13 70 (-85)
def step70 : Step := mkStep 62 53 7 63 216 193 7 234 (-121) 43
def step71 : Step := mkStep 57 29 38 28 84 102 12 124 (-45) 20
def step72 : Step := mkStep 47 47 48 46 199 207 207 199 (-14) 17
def step73 : Step := mkStep 38 38 52 21 81 133 133 81 14 (-17)
def step74 : Step := mkStep 48 61 63 9 151 218 206 27 8 (-79)
def step75 : Step := mkStep 27 4 32 48 93 9 111 177 9 93
def step76 : Step := mkStep 52 5 24 47 217 21 111 177 (-53) 99
def step77 : Step := mkStep 56 5 4 57 200 35 7 234 (-98) 119
def step78 : Step := mkStep 48 18 12 37 228 69 91 132 (-73) 54
def step79 : Step := mkStep 15 56 33 43 92 181 153 126 14 (-17)
def step80 : Step := mkStep 47 15 21 58 200 35 97 194 (-53) 99
def step81 : Step := mkStep 45 28 2 40 233 179 83 211 (-90) 40
def step82 : Step := mkStep 25 62 44 47 103 229 173 171 14 (-17)
def step83 : Step := mkStep 44 25 11 61 149 77 21 217 (-70) 85
def step84 : Step := mkStep 28 26 40 11 30 175 91 132 14 (-17)
def step85 : Step := mkStep 42 50 36 59 30 175 7 234 (-28) 34
def step86 : Step := mkStep 59 57 33 15 154 187 51 42 (-68) (-56)
def step87 : Step := mkStep 51 8 0 61 217 21 21 217 (-98) 119
def step88 : Step := mkStep 40 42 4 13 236 148 96 22 (-82) (-39)
def step89 : Step := mkStep 19 25 31 12 72 226 142 174 14 (-17)
def step90 : Step := mkStep 39 39 13 34 208 114 102 84 (-62) 6
def step91 : Step := mkStep 33 37 47 21 25 65 65 25 14 (-17)
def step92 : Step := mkStep 37 12 18 48 155 15 77 149 (-39) 82
def step93 : Step := mkStep 62 24 27 40 242 86 108 146 (-73) 54
def step94 : Step := mkStep 36 49 3 37 160 125 23 76 (-79) (-8)
def step95 : Step := mkStep 0 62 49 16 44 192 220 10 70 (-85)
def step96 : Step := mkStep 35 46 12 58 228 69 119 98 (-59) 37
def step97 : Step := mkStep 29 21 40 6 64 147 119 98 14 (-17)
def step98 : Step := mkStep 34 22 8 51 118 74 18 186 (-56) 68
def step99 : Step := mkStep 63 60 8 53 227 241 21 217 (-124) 12
def step100 : Step := mkStep 33 50 24 28 95 150 54 73 (-34) (-28)
def step101 : Step := mkStep 20 27 16 15 104 57 79 8 (-17) (-14)
def step102 : Step := mkStep 15 53 62 4 24 237 209 58 70 (-85)
def step103 : Step := mkStep 11 60 61 28 27 206 212 89 73 (-54)
def step104 : Step := mkStep 61 58 17 1 213 224 48 11 (-102) (-84)
def step105 : Step := mkStep 31 22 56 63 118 74 210 230 40 90
def step106 : Step := mkStep 46 55 63 36 55 240 128 191 14 (-17)
def step107 : Step := mkStep 33 29 11 0 151 218 88 101 (-51) (-42)
def step108 : Step := mkStep 31 63 50 47 134 232 204 168 14 (-17)
def step109 : Step := mkStep 22 11 18 32 203 4 178 61 (-11) 48
def step110 : Step := mkStep 34 22 45 6 163 94 206 27 14 (-17)
def step111 : Step := mkStep 32 56 2 61 222 131 91 132 (-76) 23
def step112 : Step := mkStep 60 36 48 9 222 131 175 30 (-34) (-28)
def step113 : Step := mkStep 18 21 29 8 39 82 82 39 14 (-17)
def step114 : Step := mkStep 31 63 5 10 165 235 65 25 (-71) (-87)
def step115 : Step := mkStep 51 23 62 4 118 74 158 16 14 (-17)
def step116 : Step := mkStep 31 23 29 42 143 139 145 205 (-11) 48
def step117 : Step := mkStep 30 51 45 19 19 127 65 25 11 (-48)
def step118 : Step := mkStep 30 39 1 3 199 207 99 53 (-68) (-56)
def step119 : Step := mkStep 29 36 10 24 135 60 48 11 (-48) (-11)
def step120 : Step := mkStep 37 59 15 54 120 215 35 200 (-62) 6
def step121 : Step := mkStep 26 46 0 27 163 94 48 11 (-65) (-25)
def step122 : Step := mkStep 51 58 27 34 132 91 17 14 (-65) (-25)
def step123 : Step := mkStep 58 19 0 63 231 38 4 203 (-115) 105
def step124 : Step := mkStep 25 1 10 14 186 18 130 50 (-28) 34
def step125 : Step := mkStep 21 41 9 5 75 195 37 59 (-37) (-59)
def step126 : Step := mkStep 42 59 60 41 30 175 91 132 14 (-17)
def step127 : Step := mkStep 26 37 31 15 36 113 51 42 (-3) (-31)
def step128 : Step := mkStep 62 47 6 57 216 193 7 234 (-121) 43
def step129 : Step := mkStep 3 2 59 62 31 3 241 227 105 115
def step130 : Step := mkStep 61 56 63 52 39 82 26 107 (-14) 17
def step131 : Step := mkStep 26 28 62 3 81 133 223 41 59 (-37)
def step132 : Step := mkStep 50 1 18 11 208 114 108 146 (-59) 37
def step133 : Step := mkStep 26 6 24 59 203 4 190 185 (-5) 110
def step134 : Step := mkStep 59 59 8 11 196 238 6 62 (-116) (-67)
def step135 : Step := mkStep 25 20 36 6 84 102 130 50 14 (-17)
def step136 : Step := mkStep 25 43 9 48 149 77 71 87 (-45) 20
def step137 : Step := mkStep 24 62 56 13 55 240 178 61 39 (-82)
def step138 : Step := mkStep 12 54 59 6 13 189 189 13 70 (-85)
def step139 : Step := mkStep 24 19 5 41 112 136 52 214 (-42) 51
def step140 : Step := mkStep 14 1 59 35 31 3 201 137 85 70
def step141 : Step := mkStep 55 8 11 51 169 32 4 203 (-84) 102
def step142 : Step := mkStep 6 34 20 23 25 65 65 25 14 (-17)
def step143 : Step := mkStep 23 47 21 18 106 198 102 84 (-20) (-45)
def step144 : Step := mkStep 59 60 4 54 213 224 4 203 (-124) 12
def step145 : Step := mkStep 23 7 45 50 90 40 176 202 40 90
def step146 : Step := mkStep 13 4 24 25 124 12 164 78 20 45
def step147 : Step := mkStep 49 29 61 10 104 57 141 2 14 (-17)
def step148 : Step := mkStep 21 60 2 0 72 226 0 0 (-57) (-104)
def step149 : Step := mkStep 36 54 59 12 106 198 192 44 25 (-65)
def step150 : Step := mkStep 57 41 40 40 236 148 170 140 (-45) 20
def step151 : Step := mkStep 21 41 39 60 118 74 170 140 20 45
def step152 : Step := mkStep 1 19 3 2 106 198 136 112 (-3) (-31)
def step153 : Step := mkStep 25 16 35 2 10 220 80 180 14 (-17)
def step154 : Step := mkStep 21 20 26 32 132 91 153 126 3 31
def step155 : Step := mkStep 13 19 24 7 129 122 178 61 14 (-17)
def step156 : Step := mkStep 20 48 42 9 41 223 133 81 25 (-65)
def step157 : Step := mkStep 19 2 0 58 200 35 131 222 (-36) 113
def step158 : Step := mkStep 27 26 2 56 115 105 21 217 (-56) 68
def step159 : Step := mkStep 12 42 2 24 112 136 68 56 (-34) (-28)
def step160 : Step := mkStep 2 62 45 41 67 116 206 27 59 (-37)
def step161 : Step := mkStep 24 27 36 13 22 96 68 56 14 (-17)
def step162 : Step := mkStep 39 15 37 49 228 69 221 182 (-8) 79
def step163 : Step := mkStep 13 20 24 8 39 82 82 39 14 (-17)
def step164 : Step := mkStep 18 42 60 51 13 189 179 233 65 25
def step165 : Step := mkStep 63 60 3 4 230 210 0 0 (-133) (-81)
def step166 : Step := mkStep 1 54 19 44 118 74 158 16 14 (-17)
def step167 : Step := mkStep 63 60 3 4 227 241 3 31 (-133) (-81)
def step168 : Step := mkStep 21 54 53 22 75 195 195 75 42 (-51)
def step169 : Step := mkStep 20 16 30 3 104 57 141 2 14 (-17)
def step170 : Step := mkStep 17 18 56 44 67 116 224 213 68 56
def step171 : Step := mkStep 20 6 18 60 200 35 193 216 (-5) 110
def step172 : Step := mkStep 50 10 51 0 64 147 91 132 0 0
def step173 : Step := mkStep 35 17 45 1 41 223 111 177 14 (-17)
def step174 : Step := mkStep 39 13 26 23 172 1 113 36 (-28) 34
def step175 : Step := mkStep 3 3 59 63 31 3 241 227 105 115
def step176 : Step := mkStep 16 3 21 49 203 4 218 151 9 93
def step177 : Step := mkStep 10 48 19 45 87 71 99 53 0 0
def step178 : Step := mkStep 15 40 6 38 103 229 83 211 (-31) 3
def step179 : Step := mkStep 56 3 29 61 172 1 69 228 (-50) 130
def step180 : Step := mkStep 21 38 28 33 134 232 176 202 0 0
def step181 : Step := mkStep 23 47 61 6 89 212 240 55 56 (-68)
def step182 : Step := mkStep 62 2 2 62 234 7 7 234 (-112) 136
def step183 : Step := mkStep 54 11 11 54 169 32 4 203 (-84) 102
def step184 : Step := mkStep 14 63 63 14 13 189 189 13 70 (-85)
def step185 : Step := mkStep 21 38 4 44 155 15 65 25 (-45) 20
def step186 : Step := mkStep 14 28 46 47 11 48 122 129 51 42
def step187 : Step := mkStep 61 3 16 45 197 66 38 231 (-84) 102
def step188 : Step := mkStep 35 60 41 3 24 237 51 42 (-9) (-93)
def step189 : Step := mkStep 36 17 46 1 55 240 128 191 14 (-17)
def step190 : Step := mkStep 11 61 34 7 10 220 96 22 22 (-96)
def step191 : Step := mkStep 13 56 62 24 50 130 220 10 73 (-54)
def step192 : Step := mkStep 50 0 3 28 183 49 15 155 (-87) 71
def step193 : Step := mkStep 27 25 0 39 177 111 77 149 (-59) 37
def step194 : Step := mkStep 13 44 18 8 213 224 240 55 (-6) (-62)
def step195 : Step := mkStep 54 12 2 48 228 69 35 200 (-101) 88
def step196 : Step := mkStep 13 13 11 52 234 7 215 120 (-8) 79
def step197 : Step := mkStep 12 62 40 57 87 71 161 47 31 (-3)
def step198 : Step := mkStep 22 11 40 5 28 34 96 22 31 (-3)
def step199 : Step := mkStep 6 28 17 1 92 181 147 64 11 (-48)
def step200 : Step := mkStep 12 32 58 17 24 237 221 182 76 (-23)
def step201 : Step := mkStep 60 62 2 23 233 179 3 31 (-130) (-50)
def step202 : Step := mkStep 42 58 60 40 42 51 79 8 14 (-17)
def step203 : Step := mkStep 11 38 36 50 169 32 240 55 34 28
def step204 : Step := mkStep 11 8 54 10 73 54 240 55 79 8
def step205 : Step := mkStep 50 38 43 62 121 43 77 149 (-25) 65
def step206 : Step := mkStep 43 34 19 61 146 108 52 214 (-56) 68
def step207 : Step := mkStep 10 54 8 11 134 232 130 50 (-23) (-76)
def step208 : Step := mkStep 54 27 54 58 194 97 193 216 (-8) 79
def step209 : Step := mkStep 10 23 1 55 121 43 77 149 (-25) 65
def step210 : Step := mkStep 7 36 3 10 188 159 175 30 (-20) (-45)
def step211 : Step := mkStep 14 50 22 30 137 201 167 109 (-3) (-31)
def step212 : Step := mkStep 10 14 32 43 36 113 131 222 37 59
def step213 : Step := mkStep 60 10 9 61 203 4 4 203 (-98) 119
def step214 : Step := mkStep 8 48 26 53 177 111 229 103 17 14
def step215 : Step := mkStep 63 5 20 63 203 4 38 231 (-81) 133
def step216 : Step := mkStep 10 45 26 33 39 82 82 39 14 (-17)
def step217 : Step := mkStep 6 52 38 23 106 198 226 72 42 (-51)
def step218 : Step := mkStep 11 37 31 0 123 184 206 27 25 (-65)
def step219 : Step := mkStep 30 22 41 7 149 77 189 13 14 (-17)
def step220 : Step := mkStep 6 12 62 55 31 3 235 165 102 84
def step221 : Step := mkStep 44 42 60 40 149 77 195 75 17 14
def step222 : Step := mkStep 6 0 18 39 8 79 69 228 23 76
def step223 : Step := mkStep 29 20 37 63 124 12 142 174 9 93
def step224 : Step := mkStep 5 58 16 56 58 209 97 194 0 0
def step225 : Step := mkStep 5 49 47 44 58 209 221 182 62 (-6)
def step226 : Step := mkStep 0 56 18 46 2 141 57 104 14 (-17)
def step227 : Step := mkStep 5 37 3 28 42 51 17 14 (-17) (-14)
def step228 : Step := mkStep 1 62 59 23 30 175 237 24 87 (-71)
def step229 : Step := mkStep 53 32 49 14 233 179 229 103 (-17) (-14)
def step230 : Step := mkStep 45 34 5 62 177 111 21 217 (-87) 71
def step231 : Step := mkStep 60 0 13 26 166 63 1 172 (-87) 71
def step232 : Step := mkStep 5 28 34 16 109 167 229 103 45 (-20)
def step233 : Step := mkStep 62 41 0 2 233 179 3 31 (-130) (-50)
def step234 : Step := mkStep 32 43 13 14 165 235 105 115 (-51) (-42)
def step235 : Step := mkStep 48 36 27 4 78 164 6 62 (-51) (-42)
def step236 : Step := mkStep 3 53 59 14 27 206 240 55 87 (-71)
def step237 : Step := mkStep 10 10 61 3 42 51 237 24 93 (-9)
def step238 : Step := mkStep 52 8 45 7 157 156 156 157 (-14) 17
def step239 : Step := mkStep 3 22 52 58 39 82 224 213 85 70
def step240 : Step := mkStep 19 1 44 3 0 0 96 22 48 11
def step241 : Step := mkStep 62 8 0 35 222 131 7 234 (-118) 74
def step242 : Step := mkStep 20 56 38 42 146 108 192 44 14 (-17)
def step243 : Step := mkStep 3 10 8 42 183 49 201 137 6 62
def step244 : Step := mkStep 8 14 48 58 56 68 210 230 71 87
def step245 : Step := mkStep 61 59 4 36 239 117 3 31 (-127) (-19)
def step246 : Step := mkStep 2 38 24 19 13 189 105 115 28 (-34)
def step247 : Step := mkStep 60 49 7 1 216 193 17 14 (-116) (-67)
def step248 : Step := mkStep 54 29 11 39 225 100 60 135 (-90) 40
def step249 : Step := mkStep 1 56 56 1 24 237 237 24 84 (-102)
def step250 : Step := mkStep 3 40 40 3 10 220 164 78 56 (-68)
def step251 : Step := mkStep 48 42 3 4 199 207 37 59 (-99) (-53)
def step252 : Step := mkStep 12 10 60 61 28 34 210 230 88 101
def step253 : Step := mkStep 23 22 34 8 11 48 48 11 14 (-17)
def step254 : Step := mkStep 46 1 41 34 121 43 111 177 (-8) 79
def step255 : Step := mkStep 2 29 55 7 2 141 209 58 90 (-40)
def step256 : Step := mkStep 12 5 59 56 31 3 207 199 88 101
def step257 : Step := mkStep 22 40 56 57 78 164 210 230 51 42
def step258 : Step := mkStep 2 7 17 63 138 29 193 216 26 107
def step259 : Step := mkStep 0 9 51 4 28 34 220 10 93 (-9)
def step260 : Step := mkStep 19 16 59 58 28 34 176 202 71 87
def step261 : Step := mkStep 15 55 6 20 41 223 9 93 (-37) (-59)
def step262 : Step := mkStep 25 61 6 0 72 226 0 0 (-57) (-104)
def step263 : Step := mkStep 23 0 57 9 33 144 190 185 65 25
def step264 : Step := mkStep 18 1 24 63 155 15 179 233 12 124
def step265 : Step := mkStep 24 63 43 48 2 141 57 104 14 (-17)
def step266 : Step := mkStep 1 44 2 52 165 235 179 233 (-14) 17
def step267 : Step := mkStep 24 21 35 7 89 212 156 157 14 (-17)
def step268 : Step := mkStep 1 37 63 6 2 141 237 24 104 (-57)
def step269 : Step := mkStep 42 2 34 3 56 68 40 90 (-14) 17
def step270 : Step := mkStep 1 35 33 40 27 206 162 219 48 11
def step271 : Step := mkStep 51 2 6 46 231 38 66 197 (-84) 102
def step272 : Step := mkStep 35 40 48 7 171 173 223 41 11 (-48)
def step273 : Step := mkStep 1 5 51 0 16 158 232 134 93 (-9)
def step274 : Step := mkStep 13 55 2 4 89 212 48 11 (-40) (-90)
def step275 : Step := mkStep 63 58 6 35 227 241 15 155 (-127) (-19)
def step276 : Step := mkStep 2 40 39 3 44 192 192 44 56 (-68)
def step277 : Step := mkStep 2 0 63 35 0 0 232 134 116 67
def step278 : Step := mkStep 17 10 2 8 166 63 113 36 (-31) 3
def step279 : Step := mkStep 11 1 5 24 146 108 142 174 (-11) 48
def step280 : Step := mkStep 0 63 49 17 41 223 223 41 70 (-85)
def step281 : Step := mkStep 5 6 36 60 90 40 210 230 57 104
def step282 : Step := mkStep 19 63 38 49 55 240 128 191 14 (-17)
def step283 : Step := mkStep 3 31 61 58 11 48 218 151 99 53
def step284 : Step := mkStep 21 48 37 34 58 209 125 160 14 (-17)
def step285 : Step := mkStep 1 14 60 0 8 79 237 24 107 (-26)
def step286 : Step := mkStep 62 27 60 40 90 40 74 118 (-11) 48
def step287 : Step := mkStep 0 60 14 1 24 237 79 8 5 (-110)
def step288 : Step := mkStep 43 20 55 19 160 125 215 120 17 14
def step289 : Step := mkStep 30 58 21 20 47 161 3 31 (-37) (-59)
def step290 : Step := mkStep 0 2 60 21 0 0 226 72 113 36
def step291 : Step := mkStep 63 4 27 53 138 29 7 234 (-67) 116
def step292 : Step := mkStep 62 56 39 46 109 167 15 155 (-62) 6
def step293 : Step := mkStep 61 17 8 35 194 97 1 172 (-104) 57
def step294 : Step := mkStep 31 53 48 37 16 158 74 118 14 (-17)
def step295 : Step := mkStep 16 3 58 4 45 20 206 27 79 8
def step296 : Step := mkStep 13 22 17 19 182 221 221 182 0 0
def step297 : Step := mkStep 4 42 18 15 106 198 164 78 11 (-48)
def step298 : Step := mkStep 12 13 38 0 8 79 113 36 45 (-20)
def step299 : Step := mkStep 3 18 14 8 163 94 206 27 14 (-17)
def step300 : Step := mkStep 57 55 14 15 230 210 68 56 (-99) (-53)
def step301 : Step := mkStep 53 41 0 11 236 148 34 28 (-113) (-36)
def step302 : Step := mkStep 59 59 4 53 213 224 4 203 (-124) 12
def step303 : Step := mkStep 9 3 35 7 45 20 144 33 48 11
def step304 : Step := mkStep 2 40 17 30 104 57 141 2 14 (-17)
def step305 : Step := mkStep 27 58 49 1 24 237 113 36 22 (-96)
def step306 : Step := mkStep 23 53 4 9 89 212 20 45 (-54) (-73)
def step307 : Step := mkStep 12 53 59 5 44 192 220 10 70 (-85)
def step308 : Step := mkStep 20 54 25 0 58 209 79 8 (-9) (-93)
def step309 : Step := mkStep 35 63 0 2 134 232 0 0 (-88) (-101)
def step310 : Step := mkStep 50 41 17 43 219 162 94 163 (-76) 23
def step311 : Step := mkStep 36 58 54 41 25 65 65 25 14 (-17)
def step312 : Step := mkStep 8 54 2 53 183 49 127 19 (-31) 3
def step313 : Step := mkStep 0 61 56 6 24 237 237 24 84 (-102)
def step314 : Step := mkStep 23 5 25 17 231 38 240 55 3 31
def step315 : Step := mkStep 2 37 49 24 41 223 235 165 76 (-23)
def step316 : Step := mkStep 10 52 33 15 154 187 237 24 25 (-65)
def step317 : Step := mkStep 16 21 48 56 76 23 187 154 54 73
def step318 : Step := mkStep 25 24 38 26 62 6 96 22 17 14
def step319 : Step := mkStep 14 21 25 9 8 79 51 42 14 (-17)
def step320 : Step := mkStep 13 1 56 19 25 65 201 137 82 39
def step321 : Step := mkStep 55 10 4 62 203 4 4 203 (-98) 119
def step322 : Step := mkStep 9 57 0 23 41 223 9 93 (-37) (-59)
def step323 : Step := mkStep 3 59 42 5 10 220 158 16 53 (-99)
def step324 : Step := mkStep 9 23 58 58 31 3 201 137 85 70
def step325 : Step := mkStep 47 0 36 58 203 4 162 219 (-19) 127
def step326 : Step := mkStep 40 59 58 41 72 226 142 174 14 (-17)
def step327 : Step := mkStep 30 5 53 63 62 6 148 236 43 121
def step328 : Step := mkStep 21 60 41 62 42 51 85 70 17 14
def step329 : Step := mkStep 2 6 61 8 0 0 220 10 110 5
def step330 : Step := mkStep 39 29 51 12 42 51 79 8 14 (-17)
def step331 : Step := mkStep 1 1 40 63 0 0 148 236 74 118
def step332 : Step := mkStep 26 43 41 28 5 110 54 73 14 (-17)
def step333 : Step := mkStep 0 29 56 40 11 48 212 89 96 22
def step334 : Step := mkStep 63 16 4 59 228 69 7 234 (-115) 105
def step335 : Step := mkStep 16 61 44 55 14 17 79 8 31 (-3)
def step336 : Step := mkStep 1 63 32 2 24 237 141 2 36 (-113)
def step337 : Step := mkStep 31 17 41 2 118 74 158 16 14 (-17)
def step338 : Step := mkStep 22 6 57 15 107 26 240 55 65 25

def firstStep : Step := step0


def checkPrefix : List Step → ℤ → ℤ → ℤ → ℤ → Bool
  | [], k, l, m, n => decide (k = m ∧ l = n)
  | s :: ss, k, l, m, n => checkStep s k l && checkPrefix ss s.next.1 s.next.2 m n

lemma checkPath_append (xs ys : List Step) (k l m n : ℤ)
    (h : checkPrefix xs k l m n = true) (hy : checkPath ys m n = true) :
    checkPath (xs ++ ys) k l = true := by
  induction xs generalizing k l with
  | nil =>
    have he : k = m ∧ l = n := of_decide_eq_true h
    rcases he with ⟨rfl, rfl⟩
    exact hy
  | cons x xs ih =>
    have hh : checkStep x k l = true ∧ checkPrefix xs x.next.1 x.next.2 m n = true := by
      simpa only [checkPrefix, Bool.and_eq_true_iff] using h
    simp only [List.cons_append, checkPath, Bool.and_eq_true_iff]
    exact ⟨hh.1, ih _ _ hh.2⟩


def block0 : List Step := [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step9, step9, step9, step9, step9, step9, step9, step10, step11, step12]
lemma block0_checked : checkPrefix block0 (0) (0) (93) (-9) = true := by decide
def block1 : List Step := [step13, step14, step15, step5, step6, step15, step5, step6, step15, step5, step6, step15, step5, step6, step15, step5, step6, step16, step17, step18]
lemma block1_checked : checkPrefix block1 (93) (-9) (-104) (57) = true := by decide
def block2 : List Step := [step19, step20, step16, step17, step18, step19, step20, step16, step21, step22, step16, step21, step22, step16, step21, step22, step16, step21, step22, step16]
lemma block2_checked : checkPrefix block2 (-104) (57) (-87) (71) = true := by decide
def block3 : List Step := [step21, step22, step23, step20, step23, step20, step23, step20, step23, step20, step23, step20, step23, step20, step24, step25, step24, step25, step24, step25]
lemma block3_checked : checkPrefix block3 (-87) (71) (14) (-17) = true := by decide
def block4 : List Step := [step24, step25, step24, step25, step26, step18, step27, step28, step26, step18, step27, step28, step26, step18, step29, step30, step10, step31, step32, step33]
lemma block4_checked : checkPrefix block4 (14) (-17) (-118) (74) = true := by decide
def block5 : List Step := [step10, step31, step32, step33, step10, step31, step32, step33, step10, step31, step32, step33, step10, step34, step26, step18, step29, step35, step26, step18]
lemma block5_checked : checkPrefix block5 (-118) (74) (-104) (57) = true := by decide
def block6 : List Step := [step29, step35, step26, step36, step37, step38, step39, step3, step4, step5, step6, step26, step36, step37, step40, step41, step42, step26, step36, step37]
lemma block6_checked : checkPrefix block6 (-104) (57) (-84) (102) = true := by decide
def block7 : List Step := [step40, step43, step26, step36, step37, step40, step43, step26, step36, step37, step40, step43, step26, step36, step37, step40, step43, step26, step36, step37]
lemma block7_checked : checkPrefix block7 (-84) (102) (-84) (102) = true := by decide
def block8 : List Step := [step40, step43, step26, step44, step45, step26, step44, step46, step47, step26, step44, step46, step47, step48, step4, step49, step50, step48, step4, step49]
lemma block8_checked : checkPrefix block8 (-84) (102) (34) (28) = true := by decide
def block9 : List Step := [step50, step48, step4, step49, step50, step48, step51, step40, step43, step48, step51, step40, step43, step48, step51, step40, step43, step48, step51, step40]
lemma block9_checked : checkPrefix block9 (34) (28) (-98) (119) = true := by decide

def block10 : List Step := [step43, step48, step52, step53, step54, step55, step56, step43, step54, step55, step56, step43, step54, step55, step56, step43, step54, step55, step57, step58]
lemma block10_checked : checkPrefix block10 (-98) (119) (-81) (133) = true := by decide
def block11 : List Step := [step34, step54, step55, step57, step58, step34, step54, step55, step57, step58, step34, step54, step55, step57, step58, step59, step60, step61, step62, step63]
lemma block11_checked : checkPrefix block11 (-81) (133) (-31) (3) = true := by decide
def block12 : List Step := [step64, step65, step3, step66, step67, step68, step40, step43, step62, step63, step64, step65, step3, step66, step67, step68, step40, step43, step62, step63]
lemma block12_checked : checkPrefix block12 (-31) (3) (-31) (3) = true := by decide
def block13 : List Step := [step64, step65, step3, step66, step67, step68, step40, step43, step62, step63, step69, step70, step71, step37, step40, step43, step62, step63, step69, step70]
lemma block13_checked : checkPrefix block13 (-31) (3) (-121) (43) = true := by decide
def block14 : List Step := [step72, step73, step74, step75, step76, step12, step13, step14, step74, step75, step76, step12, step13, step14, step74, step75, step76, step12, step77, step43]
lemma block14_checked : checkPrefix block14 (-121) (43) (14) (-17) = true := by decide
def block15 : List Step := [step78, step79, step80, step12, step77, step43, step80, step12, step77, step43, step80, step12, step77, step43, step80, step12, step77, step43, step81, step82]
lemma block15_checked : checkPrefix block15 (14) (-17) (14) (-17) = true := by decide
def block16 : List Step := [step83, step84, step83, step84, step83, step84, step83, step84, step83, step84, step83, step84, step83, step84, step85, step86, step87, step43, step85, step86]
lemma block16_checked : checkPrefix block16 (14) (-17) (-68) (-56) = true := by decide
def block17 : List Step := [step87, step43, step85, step86, step87, step43, step85, step86, step87, step43, step88, step89, step90, step91, step90, step91, step90, step91, step90, step91]
lemma block17_checked : checkPrefix block17 (-68) (-56) (14) (-17) = true := by decide
def block18 : List Step := [step90, step91, step90, step91, step90, step91, step90, step91, step90, step91, step92, step93, step79, step94, step95, step70, step72, step73, step96, step97]
lemma block18_checked : checkPrefix block18 (14) (-17) (14) (-17) = true := by decide
def block19 : List Step := [step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97]
lemma block19_checked : checkPrefix block19 (14) (-17) (14) (-17) = true := by decide

def block20 : List Step := [step96, step97, step96, step97, step96, step97, step96, step97, step98, step99, step14, step98, step99, step14, step98, step99, step14, step98, step99, step14]
lemma block20_checked : checkPrefix block20 (14) (-17) (14) (-17) = true := by decide
def block21 : List Step := [step100, step33, step10, step101, step65, step3, step66, step67, step68, step40, step43, step100, step33, step10, step102, step70, step72, step73, step100, step33]
lemma block21_checked : checkPrefix block21 (14) (-17) (-118) (74) = true := by decide
def block22 : List Step := [step10, step103, step104, step25, step100, step33, step10, step103, step104, step25, step100, step33, step10, step103, step104, step25, step100, step33, step10, step103]
lemma block22_checked : checkPrefix block22 (-118) (74) (73) (-54) = true := by decide
def block23 : List Step := [step104, step25, step100, step33, step10, step103, step104, step25, step100, step33, step105, step106, step107, step108, step107, step108, step107, step108, step107, step108]
lemma block23_checked : checkPrefix block23 (73) (-54) (14) (-17) = true := by decide
def block24 : List Step := [step107, step108, step107, step108, step107, step108, step107, step108, step107, step108, step107, step108, step107, step108, step107, step109, step46, step91, step107, step109]
lemma block24_checked : checkPrefix block24 (14) (-17) (-11) (48) = true := by decide
def block25 : List Step := [step110, step111, step112, step33, step105, step113, step111, step112, step33, step105, step113, step114, step115, step116, step110, step116, step110, step116, step110, step116]
lemma block25_checked : checkPrefix block25 (-11) (48) (-11) (48) = true := by decide
def block26 : List Step := [step110, step116, step110, step116, step110, step116, step110, step117, step53, step117, step53, step117, step53, step117, step53, step117, step53, step117, step53, step118]
lemma block26_checked : checkPrefix block26 (-11) (48) (-68) (-56) = true := by decide
def block27 : List Step := [step87, step43, step118, step87, step43, step118, step87, step43, step118, step87, step43, step118, step87, step43, step118, step87, step43, step119, step120, step91]
lemma block27_checked : checkPrefix block27 (-68) (-56) (14) (-17) = true := by decide
def block28 : List Step := [step119, step120, step91, step119, step120, step91, step119, step120, step91, step121, step122, step122, step123, step3, step66, step124, step125, step126, step127, step128]
lemma block28_checked : checkPrefix block28 (14) (-17) (-121) (43) = true := by decide
def block29 : List Step := [step72, step73, step127, step128, step72, step73, step127, step128, step72, step73, step127, step128, step129, step130, step73, step127, step128, step129, step130, step73]
lemma block29_checked : checkPrefix block29 (-121) (43) (14) (-17) = true := by decide

def block30 : List Step := [step131, step132, step97, step131, step132, step97, step131, step132, step97, step131, step132, step97, step131, step132, step97, step133, step134, step135, step133, step134]
lemma block30_checked : checkPrefix block30 (14) (-17) (-116) (-67) = true := by decide
def block31 : List Step := [step135, step133, step134, step135, step136, step37, step40, step43, step137, step138, step70, step129, step130, step73, step139, step68, step40, step140, step141, step40]
lemma block31_checked : checkPrefix block31 (-116) (-67) (-98) (119) = true := by decide
def block32 : List Step := [step142, step139, step68, step40, step142, step139, step68, step40, step142, step139, step68, step40, step142, step139, step68, step40, step142, step139, step68, step40]
lemma block32_checked : checkPrefix block32 (-98) (119) (-98) (119) = true := by decide
def block33 : List Step := [step142, step139, step68, step40, step142, step143, step144, step14, step143, step144, step14, step143, step144, step14, step145, step113, step145, step113, step145, step113]
lemma block33_checked : checkPrefix block33 (-98) (119) (14) (-17) = true := by decide
def block34 : List Step := [step145, step146, step147, step145, step146, step147, step148, step149, step150, step37, step40, step142, step151, step147, step151, step147, step151, step147, step151, step152]
lemma block34_checked : checkPrefix block34 (14) (-17) (-3) (-31) = true := by decide
def block35 : List Step := [step153, step151, step152, step153, step151, step152, step153, step154, step39, step3, step155, step156, step150, step37, step40, step142, step156, step150, step37, step40]
lemma block35_checked : checkPrefix block35 (-3) (-31) (-98) (119) = true := by decide
def block36 : List Step := [step142, step157, step32, step33, step105, step146, step152, step153, step157, step32, step33, step105, step146, step152, step153, step157, step158, step99, step14, step157]
lemma block36_checked : checkPrefix block36 (-98) (119) (-36) (113) = true := by decide
def block37 : List Step := [step158, step99, step14, step157, step158, step99, step14, step157, step158, step99, step14, step157, step158, step99, step14, step157, step158, step99, step14, step157]
lemma block37_checked : checkPrefix block37 (-36) (113) (-36) (113) = true := by decide
def block38 : List Step := [step158, step159, step33, step105, step146, step152, step160, step161, step157, step158, step159, step162, step163, step164, step165, step166, step164, step165, step166, step164]
lemma block38_checked : checkPrefix block38 (-36) (113) (65) (25) = true := by decide
def block39 : List Step := [step165, step166, step164, step165, step166, step164, step165, step166, step164, step165, step166, step164, step167, step166, step164, step167, step166, step164, step168, step169]
lemma block39_checked : checkPrefix block39 (65) (25) (14) (-17) = true := by decide

def block40 : List Step := [step164, step168, step169, step170, step171, step134, step135, step170, step171, step134, step135, step170, step171, step172, step173, step170, step171, step172, step173, step170]
lemma block40_checked : checkPrefix block40 (14) (-17) (68) (56) = true := by decide
def block41 : List Step := [step171, step172, step173, step170, step171, step174, step125, step126, step170, step171, step174, step125, step126, step170, step171, step174, step125, step126, step170, step171]
lemma block41_checked : checkPrefix block41 (68) (56) (-5) (110) = true := by decide
def block42 : List Step := [step174, step175, step130, step73, step170, step171, step174, step175, step130, step73, step176, step76, step12, step77, step142, step176, step76, step12, step77, step142]
lemma block42_checked : checkPrefix block42 (-5) (110) (14) (-17) = true := by decide
def block43 : List Step := [step176, step76, step12, step77, step142, step176, step177, step173, step176, step177, step173, step176, step177, step173, step178, step69, step70, step129, step130, step73]
lemma block43_checked : checkPrefix block43 (14) (-17) (14) (-17) = true := by decide
def block44 : List Step := [step178, step69, step179, step180, step173, step178, step69, step181, step182, step183, step40, step142, step178, step69, step181, step182, step183, step40, step142, step178]
lemma block44_checked : checkPrefix block44 (14) (-17) (-31) (3) = true := by decide
def block45 : List Step := [step69, step181, step182, step183, step40, step142, step178, step69, step181, step182, step184, step181, step182, step184, step185, step37, step40, step142, step186, step187]
lemma block45_checked : checkPrefix block45 (-31) (3) (-84) (102) = true := by decide
def block46 : List Step := [step40, step142, step186, step187, step40, step142, step186, step188, step189, step186, step188, step189, step186, step188, step189, step186, step188, step189, step186, step190]
lemma block46_checked : checkPrefix block46 (-84) (102) (22) (-96) = true := by decide
def block47 : List Step := [step22, step186, step190, step22, step191, step104, step25, step191, step104, step25, step191, step192, step21, step22, step191, step193, step97, step191, step193, step97]
lemma block47_checked : checkPrefix block47 (22) (-96) (14) (-17) = true := by decide
def block48 : List Step := [step191, step193, step97, step191, step193, step97, step191, step193, step97, step194, step195, step155, step194, step195, step155, step194, step195, step155, step194, step195]
lemma block48_checked : checkPrefix block48 (14) (-17) (-101) (88) = true := by decide
def block49 : List Step := [step155, step196, step163, step196, step163, step196, step163, step196, step163, step196, step163, step196, step163, step197, step198, step198, step198, step198, step199, step53]
lemma block49_checked : checkPrefix block49 (-101) (88) (14) (-17) = true := by decide

def block50 : List Step := [step197, step199, step53, step197, step199, step53, step197, step199, step53, step200, step201, step202, step200, step201, step202, step200, step201, step202, step200, step201]
lemma block50_checked : checkPrefix block50 (14) (-17) (-130) (-50) = true := by decide
def block51 : List Step := [step202, step200, step201, step202, step200, step201, step202, step203, step50, step203, step50, step203, step50, step203, step50, step203, step50, step203, step50, step203]
lemma block51_checked : checkPrefix block51 (-130) (-50) (34) (28) = true := by decide
def block52 : List Step := [step50, step203, step50, step204, step205, step124, step175, step130, step73, step204, step206, step159, step162, step163, step204, step206, step159, step162, step163, step207]
lemma block52_checked : checkPrefix block52 (34) (28) (-23) (-76) = true := by decide
def block53 : List Step := [step208, step163, step207, step208, step163, step207, step208, step163, step209, step124, step175, step210, step144, step14, step209, step124, step175, step210, step144, step14]
lemma block53_checked : checkPrefix block53 (-23) (-76) (14) (-17) = true := by decide
def block54 : List Step := [step209, step124, step175, step210, step144, step14, step209, step124, step175, step210, step144, step14, step209, step124, step175, step210, step144, step211, step160, step161]
lemma block54_checked : checkPrefix block54 (14) (-17) (14) (-17) = true := by decide
def block55 : List Step := [step209, step124, step175, step210, step144, step211, step160, step161, step209, step124, step175, step210, step144, step211, step160, step161, step212, step213, step142, step212]
lemma block55_checked : checkPrefix block55 (14) (-17) (37) (59) = true := by decide
def block56 : List Step := [step213, step142, step212, step213, step142, step212, step213, step142, step214, step215, step216, step214, step215, step216, step214, step215, step216, step217, step169, step217]
lemma block56_checked : checkPrefix block56 (37) (59) (42) (-51) = true := by decide
def block57 : List Step := [step169, step217, step169, step217, step169, step217, step218, step150, step37, step40, step142, step217, step218, step150, step37, step40, step142, step217, step218, step150]
lemma block57_checked : checkPrefix block57 (42) (-51) (-45) (20) = true := by decide
def block58 : List Step := [step37, step40, step142, step217, step218, step219, step217, step218, step219, step217, step218, step219, step217, step218, step219, step220, step221, step215, step216, step220]
lemma block58_checked : checkPrefix block58 (-45) (20) (102) (84) = true := by decide
def block59 : List Step := [step221, step215, step216, step220, step221, step215, step216, step220, step221, step215, step216, step220, step221, step215, step216, step220, step221, step215, step216, step220]
lemma block59_checked : checkPrefix block59 (102) (84) (102) (84) = true := by decide

def block60 : List Step := [step221, step215, step216, step220, step221, step215, step216, step222, step223, step177, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224]
lemma block60_checked : checkPrefix block60 (102) (84) (0) (0) = true := by decide
def block61 : List Step := [step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step225, step226, step225]
lemma block61_checked : checkPrefix block61 (0) (0) (62) (-6) = true := by decide
def block62 : List Step := [step226, step225, step226, step227, step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step155, step227]
lemma block62_checked : checkPrefix block62 (62) (-6) (-17) (-14) = true := by decide
def block63 : List Step := [step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step228, step229, step65, step3, step228, step229]
lemma block63_checked : checkPrefix block63 (-17) (-14) (-17) (-14) = true := by decide
def block64 : List Step := [step65, step3, step228, step229, step65, step3, step228, step229, step65, step3, step228, step229, step65, step230, step21, step22, step227, step231, step21, step22]
lemma block64_checked : checkPrefix block64 (-17) (-14) (14) (-17) = true := by decide
def block65 : List Step := [step227, step231, step21, step22, step232, step233, step202, step232, step233, step202, step232, step233, step234, step109, step110, step232, step233, step234, step109, step110]
lemma block65_checked : checkPrefix block65 (14) (-17) (14) (-17) = true := by decide
def block66 : List Step := [step232, step235, step109, step110, step232, step235, step109, step110, step232, step235, step109, step110, step236, step229, step231, step21, step22, step236, step229, step231]
lemma block66_checked : checkPrefix block66 (14) (-17) (-87) (71) = true := by decide
def block67 : List Step := [step21, step22, step236, step229, step231, step237, step77, step142, step236, step238, step73, step236, step238, step73, step236, step238, step73, step239, step141, step40]
lemma block67_checked : checkPrefix block67 (-87) (71) (-98) (119) = true := by decide
def block68 : List Step := [step142, step239, step141, step40, step142, step239, step141, step40, step142, step239, step141, step40, step142, step239, step141, step40, step142, step239, step141, step40]
lemma block68_checked : checkPrefix block68 (-98) (119) (-98) (119) = true := by decide
def block69 : List Step := [step142, step239, step141, step40, step142, step239, step240, step241, step242, step243, step244, step245, step20, step246, step57, step247, step135, step246, step57, step248]
lemma block69_checked : checkPrefix block69 (-98) (119) (-90) (40) = true := by decide

def block70 : List Step := [step82, step246, step249, step250, step182, step184, step185, step37, step40, step142, step246, step249, step250, step182, step184, step185, step251, step28, step246, step249]
lemma block70_checked : checkPrefix block70 (-90) (40) (84) (-102) = true := by decide
def block71 : List Step := [step250, step182, step184, step185, step251, step28, step246, step249, step250, step182, step184, step185, step251, step28, step246, step249, step250, step182, step184, step185]
lemma block71_checked : checkPrefix block71 (84) (-102) (-45) (20) = true := by decide
def block72 : List Step := [step251, step28, step246, step249, step250, step182, step184, step252, step253, step246, step249, step250, step254, step163, step255, step35, step255, step256, step257, step190]
lemma block72_checked : checkPrefix block72 (-45) (20) (22) (-96) = true := by decide
def block73 : List Step := [step22, step255, step256, step257, step190, step22, step258, step248, step82, step258, step248, step259, step260, step245, step20, step258, step248, step259, step260, step245]
lemma block73_checked : checkPrefix block73 (22) (-96) (-127) (-19) = true := by decide
def block74 : List Step := [step261, step126, step258, step248, step259, step260, step245, step261, step126, step258, step248, step259, step260, step245, step261, step126, step258, step248, step259, step260]
lemma block74_checked : checkPrefix block74 (-127) (-19) (71) (87) = true := by decide
def block75 : List Step := [step245, step261, step126, step258, step248, step259, step260, step245, step261, step126, step258, step248, step259, step260, step262, step263, step168, step218, step219, step258]
lemma block75_checked : checkPrefix block75 (71) (87) (26) (107) = true := by decide
def block76 : List Step := [step248, step259, step264, step265, step266, step73, step266, step267, step266, step267, step266, step267, step266, step268, step269, step267, step270, step241, step242, step270]
lemma block76_checked : checkPrefix block76 (26) (107) (48) (11) = true := by decide
def block77 : List Step := [step241, step242, step270, step241, step242, step270, step241, step242, step270, step241, step242, step270, step271, step272, step53, step273, step274, step275, step261, step126]
lemma block77_checked : checkPrefix block77 (48) (11) (14) (-17) = true := by decide
def block78 : List Step := [step273, step276, step254, step163, step273, step276, step254, step163, step273, step276, step254, step163, step273, step276, step254, step163, step273, step276, step254, step163]
lemma block78_checked : checkPrefix block78 (14) (-17) (14) (-17) = true := by decide
def block79 : List Step := [step273, step276, step254, step163, step273, step276, step254, step163, step273, step277, step278, step69, step252, step257, step190, step22, step273, step277, step278, step69]
lemma block79_checked : checkPrefix block79 (14) (-17) (70) (-85) = true := by decide

def block80 : List Step := [step252, step279, step110, step273, step277, step278, step69, step252, step279, step110, step273, step277, step278, step69, step252, step279, step110, step280, step281, step282]
lemma block80_checked : checkPrefix block80 (70) (-85) (14) (-17) = true := by decide
def block81 : List Step := [step280, step283, step284, step280, step285, step286, step110, step280, step285, step286, step110, step280, step285, step286, step110, step280, step287, step288, step215, step216]
lemma block81_checked : checkPrefix block81 (14) (-17) (14) (-17) = true := by decide
def block82 : List Step := [step280, step287, step288, step289, step126, step280, step287, step288, step289, step126, step280, step287, step288, step289, step126, step280, step287, step288, step289, step126]
lemma block82_checked : checkPrefix block82 (14) (-17) (14) (-17) = true := by decide
def block83 : List Step := [step280, step287, step288, step289, step126, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292]
lemma block83_checked : checkPrefix block83 (14) (-17) (-62) (6) = true := by decide
def block84 : List Step := [step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step293, step29]
lemma block84_checked : checkPrefix block84 (-62) (6) (90) (-40) = true := by decide
def block85 : List Step := [step256, step279, step294, step290, step293, step29, step256, step279, step295, step206, step159, step162, step163, step290, step293, step29, step256, step279, step296, step173]
lemma block85_checked : checkPrefix block85 (90) (-40) (14) (-17) = true := by decide
def block86 : List Step := [step290, step293, step29, step256, step279, step296, step173, step290, step293, step297, step53, step290, step293, step297, step53, step290, step293, step297, step298, step235]
lemma block86_checked : checkPrefix block86 (14) (-17) (-51) (-42) = true := by decide
def block87 : List Step := [step109, step296, step173, step290, step293, step299, step290, step300, step28, step290, step300, step28, step290, step300, step28, step290, step300, step28, step290, step300]
lemma block87_checked : checkPrefix block87 (-51) (-42) (-99) (-53) = true := by decide
def block88 : List Step := [step28, step290, step300, step28, step290, step300, step28, step290, step301, step302, step303, step271, step272, step304, step290, step305, step22, step290, step305, step22]
lemma block88_checked : checkPrefix block88 (-99) (-53) (14) (-17) = true := by decide
def block89 : List Step := [step290, step305, step22, step290, step305, step22, step290, step306, step307, step287, step288, step289, step126, step290, step308, step309, step310, step112, step162, step163]
lemma block89_checked : checkPrefix block89 (14) (-17) (14) (-17) = true := by decide

def block90 : List Step := [step290, step308, step309, step310, step311, step290, step308, step309, step310, step311, step290, step308, step309, step310, step311, step290, step308, step309, step310, step311]
lemma block90_checked : checkPrefix block90 (14) (-17) (14) (-17) = true := by decide
def block91 : List Step := [step290, step308, step309, step310, step312, step69, step287, step288, step313, step250, step314, step39, step230, step237, step277, step278, step69, step287, step288, step313]
lemma block91_checked : checkPrefix block91 (14) (-17) (84) (-102) = true := by decide
def block92 : List Step := [step315, step201, step234, step109, step296, step173, step290, step308, step309, step310, step312, step69, step287, step288, step313, step315, step201, step234, step109, step296]
lemma block92_checked : checkPrefix block92 (84) (-102) (0) (0) = true := by decide
def block93 : List Step := [step173, step290, step308, step316, step219, step290, step317, step318, step313, step315, step319, step290, step320, step321, step142, step290, step322, step126, step290, step322]
lemma block93_checked : checkPrefix block93 (0) (0) (-37) (-59) = true := by decide
def block94 : List Step := [step126, step290, step322, step126, step290, step322, step126, step290, step322, step126, step290, step323, step324, step240, step271, step272, step304, step290, step323, step324]
lemma block94_checked : checkPrefix block94 (-37) (-59) (85) (70) = true := by decide
def block95 : List Step := [step240, step271, step272, step304, step290, step323, step324, step240, step325, step326, step290, step323, step324, step240, step327, step328, step313, step315, step319, step290]
lemma block95_checked : checkPrefix block95 (85) (70) (113) (36) = true := by decide
def block96 : List Step := [step323, step324, step329, step330, step290, step331, step332, step290, step333, step334, step335, step336, step337, step290, step308, step316, step338, step168, step218, step338]
lemma block96_checked : checkPrefix block96 (113) (36) (65) (25) = true := by decide
def block97 : List Step := [step168, step218, step338, step168, step218, step338, step168]
lemma block97_checked : checkPrefix block97 (65) (25) (42) (-51) = true := by decide
def tail98 : List Step := []
lemma tail98_checked : checkPath tail98 42 (-51) = true := by decide
attribute [irreducible] checkPath checkPrefix checkStep
def tail97 : List Step := block97 ++ tail98
lemma tail97_checked : checkPath tail97 (65) (25) = true :=
  checkPath_append block97 tail98 (65) (25) (42) (-51) block97_checked tail98_checked
def tail96 : List Step := block96 ++ tail97
lemma tail96_checked : checkPath tail96 (113) (36) = true :=
  checkPath_append block96 tail97 (113) (36) (65) (25) block96_checked tail97_checked
def tail95 : List Step := block95 ++ tail96
lemma tail95_checked : checkPath tail95 (85) (70) = true :=
  checkPath_append block95 tail96 (85) (70) (113) (36) block95_checked tail96_checked
def tail94 : List Step := block94 ++ tail95
lemma tail94_checked : checkPath tail94 (-37) (-59) = true :=
  checkPath_append block94 tail95 (-37) (-59) (85) (70) block94_checked tail95_checked
def tail93 : List Step := block93 ++ tail94
lemma tail93_checked : checkPath tail93 (0) (0) = true :=
  checkPath_append block93 tail94 (0) (0) (-37) (-59) block93_checked tail94_checked
def tail92 : List Step := block92 ++ tail93
lemma tail92_checked : checkPath tail92 (84) (-102) = true :=
  checkPath_append block92 tail93 (84) (-102) (0) (0) block92_checked tail93_checked
def tail91 : List Step := block91 ++ tail92
lemma tail91_checked : checkPath tail91 (14) (-17) = true :=
  checkPath_append block91 tail92 (14) (-17) (84) (-102) block91_checked tail92_checked
def tail90 : List Step := block90 ++ tail91
lemma tail90_checked : checkPath tail90 (14) (-17) = true :=
  checkPath_append block90 tail91 (14) (-17) (14) (-17) block90_checked tail91_checked
def tail89 : List Step := block89 ++ tail90
lemma tail89_checked : checkPath tail89 (14) (-17) = true :=
  checkPath_append block89 tail90 (14) (-17) (14) (-17) block89_checked tail90_checked
def tail88 : List Step := block88 ++ tail89
lemma tail88_checked : checkPath tail88 (-99) (-53) = true :=
  checkPath_append block88 tail89 (-99) (-53) (14) (-17) block88_checked tail89_checked
def tail87 : List Step := block87 ++ tail88
lemma tail87_checked : checkPath tail87 (-51) (-42) = true :=
  checkPath_append block87 tail88 (-51) (-42) (-99) (-53) block87_checked tail88_checked
def tail86 : List Step := block86 ++ tail87
lemma tail86_checked : checkPath tail86 (14) (-17) = true :=
  checkPath_append block86 tail87 (14) (-17) (-51) (-42) block86_checked tail87_checked
def tail85 : List Step := block85 ++ tail86
lemma tail85_checked : checkPath tail85 (90) (-40) = true :=
  checkPath_append block85 tail86 (90) (-40) (14) (-17) block85_checked tail86_checked
def tail84 : List Step := block84 ++ tail85
lemma tail84_checked : checkPath tail84 (-62) (6) = true :=
  checkPath_append block84 tail85 (-62) (6) (90) (-40) block84_checked tail85_checked
def tail83 : List Step := block83 ++ tail84
lemma tail83_checked : checkPath tail83 (14) (-17) = true :=
  checkPath_append block83 tail84 (14) (-17) (-62) (6) block83_checked tail84_checked
def tail82 : List Step := block82 ++ tail83
lemma tail82_checked : checkPath tail82 (14) (-17) = true :=
  checkPath_append block82 tail83 (14) (-17) (14) (-17) block82_checked tail83_checked
def tail81 : List Step := block81 ++ tail82
lemma tail81_checked : checkPath tail81 (14) (-17) = true :=
  checkPath_append block81 tail82 (14) (-17) (14) (-17) block81_checked tail82_checked
def tail80 : List Step := block80 ++ tail81
lemma tail80_checked : checkPath tail80 (70) (-85) = true :=
  checkPath_append block80 tail81 (70) (-85) (14) (-17) block80_checked tail81_checked
def tail79 : List Step := block79 ++ tail80
lemma tail79_checked : checkPath tail79 (14) (-17) = true :=
  checkPath_append block79 tail80 (14) (-17) (70) (-85) block79_checked tail80_checked
def tail78 : List Step := block78 ++ tail79
lemma tail78_checked : checkPath tail78 (14) (-17) = true :=
  checkPath_append block78 tail79 (14) (-17) (14) (-17) block78_checked tail79_checked
def tail77 : List Step := block77 ++ tail78
lemma tail77_checked : checkPath tail77 (48) (11) = true :=
  checkPath_append block77 tail78 (48) (11) (14) (-17) block77_checked tail78_checked
def tail76 : List Step := block76 ++ tail77
lemma tail76_checked : checkPath tail76 (26) (107) = true :=
  checkPath_append block76 tail77 (26) (107) (48) (11) block76_checked tail77_checked
def tail75 : List Step := block75 ++ tail76
lemma tail75_checked : checkPath tail75 (71) (87) = true :=
  checkPath_append block75 tail76 (71) (87) (26) (107) block75_checked tail76_checked
def tail74 : List Step := block74 ++ tail75
lemma tail74_checked : checkPath tail74 (-127) (-19) = true :=
  checkPath_append block74 tail75 (-127) (-19) (71) (87) block74_checked tail75_checked
def tail73 : List Step := block73 ++ tail74
lemma tail73_checked : checkPath tail73 (22) (-96) = true :=
  checkPath_append block73 tail74 (22) (-96) (-127) (-19) block73_checked tail74_checked
def tail72 : List Step := block72 ++ tail73
lemma tail72_checked : checkPath tail72 (-45) (20) = true :=
  checkPath_append block72 tail73 (-45) (20) (22) (-96) block72_checked tail73_checked
def tail71 : List Step := block71 ++ tail72
lemma tail71_checked : checkPath tail71 (84) (-102) = true :=
  checkPath_append block71 tail72 (84) (-102) (-45) (20) block71_checked tail72_checked
def tail70 : List Step := block70 ++ tail71
lemma tail70_checked : checkPath tail70 (-90) (40) = true :=
  checkPath_append block70 tail71 (-90) (40) (84) (-102) block70_checked tail71_checked
def tail69 : List Step := block69 ++ tail70
lemma tail69_checked : checkPath tail69 (-98) (119) = true :=
  checkPath_append block69 tail70 (-98) (119) (-90) (40) block69_checked tail70_checked
def tail68 : List Step := block68 ++ tail69
lemma tail68_checked : checkPath tail68 (-98) (119) = true :=
  checkPath_append block68 tail69 (-98) (119) (-98) (119) block68_checked tail69_checked
def tail67 : List Step := block67 ++ tail68
lemma tail67_checked : checkPath tail67 (-87) (71) = true :=
  checkPath_append block67 tail68 (-87) (71) (-98) (119) block67_checked tail68_checked
def tail66 : List Step := block66 ++ tail67
lemma tail66_checked : checkPath tail66 (14) (-17) = true :=
  checkPath_append block66 tail67 (14) (-17) (-87) (71) block66_checked tail67_checked
def tail65 : List Step := block65 ++ tail66
lemma tail65_checked : checkPath tail65 (14) (-17) = true :=
  checkPath_append block65 tail66 (14) (-17) (14) (-17) block65_checked tail66_checked
def tail64 : List Step := block64 ++ tail65
lemma tail64_checked : checkPath tail64 (-17) (-14) = true :=
  checkPath_append block64 tail65 (-17) (-14) (14) (-17) block64_checked tail65_checked
def tail63 : List Step := block63 ++ tail64
lemma tail63_checked : checkPath tail63 (-17) (-14) = true :=
  checkPath_append block63 tail64 (-17) (-14) (-17) (-14) block63_checked tail64_checked
def tail62 : List Step := block62 ++ tail63
lemma tail62_checked : checkPath tail62 (62) (-6) = true :=
  checkPath_append block62 tail63 (62) (-6) (-17) (-14) block62_checked tail63_checked
def tail61 : List Step := block61 ++ tail62
lemma tail61_checked : checkPath tail61 (0) (0) = true :=
  checkPath_append block61 tail62 (0) (0) (62) (-6) block61_checked tail62_checked
def tail60 : List Step := block60 ++ tail61
lemma tail60_checked : checkPath tail60 (102) (84) = true :=
  checkPath_append block60 tail61 (102) (84) (0) (0) block60_checked tail61_checked
def tail59 : List Step := block59 ++ tail60
lemma tail59_checked : checkPath tail59 (102) (84) = true :=
  checkPath_append block59 tail60 (102) (84) (102) (84) block59_checked tail60_checked
def tail58 : List Step := block58 ++ tail59
lemma tail58_checked : checkPath tail58 (-45) (20) = true :=
  checkPath_append block58 tail59 (-45) (20) (102) (84) block58_checked tail59_checked
def tail57 : List Step := block57 ++ tail58
lemma tail57_checked : checkPath tail57 (42) (-51) = true :=
  checkPath_append block57 tail58 (42) (-51) (-45) (20) block57_checked tail58_checked
def tail56 : List Step := block56 ++ tail57
lemma tail56_checked : checkPath tail56 (37) (59) = true :=
  checkPath_append block56 tail57 (37) (59) (42) (-51) block56_checked tail57_checked
def tail55 : List Step := block55 ++ tail56
lemma tail55_checked : checkPath tail55 (14) (-17) = true :=
  checkPath_append block55 tail56 (14) (-17) (37) (59) block55_checked tail56_checked
def tail54 : List Step := block54 ++ tail55
lemma tail54_checked : checkPath tail54 (14) (-17) = true :=
  checkPath_append block54 tail55 (14) (-17) (14) (-17) block54_checked tail55_checked
def tail53 : List Step := block53 ++ tail54
lemma tail53_checked : checkPath tail53 (-23) (-76) = true :=
  checkPath_append block53 tail54 (-23) (-76) (14) (-17) block53_checked tail54_checked
def tail52 : List Step := block52 ++ tail53
lemma tail52_checked : checkPath tail52 (34) (28) = true :=
  checkPath_append block52 tail53 (34) (28) (-23) (-76) block52_checked tail53_checked
def tail51 : List Step := block51 ++ tail52
lemma tail51_checked : checkPath tail51 (-130) (-50) = true :=
  checkPath_append block51 tail52 (-130) (-50) (34) (28) block51_checked tail52_checked
def tail50 : List Step := block50 ++ tail51
lemma tail50_checked : checkPath tail50 (14) (-17) = true :=
  checkPath_append block50 tail51 (14) (-17) (-130) (-50) block50_checked tail51_checked
def tail49 : List Step := block49 ++ tail50
lemma tail49_checked : checkPath tail49 (-101) (88) = true :=
  checkPath_append block49 tail50 (-101) (88) (14) (-17) block49_checked tail50_checked
def tail48 : List Step := block48 ++ tail49
lemma tail48_checked : checkPath tail48 (14) (-17) = true :=
  checkPath_append block48 tail49 (14) (-17) (-101) (88) block48_checked tail49_checked
def tail47 : List Step := block47 ++ tail48
lemma tail47_checked : checkPath tail47 (22) (-96) = true :=
  checkPath_append block47 tail48 (22) (-96) (14) (-17) block47_checked tail48_checked
def tail46 : List Step := block46 ++ tail47
lemma tail46_checked : checkPath tail46 (-84) (102) = true :=
  checkPath_append block46 tail47 (-84) (102) (22) (-96) block46_checked tail47_checked
def tail45 : List Step := block45 ++ tail46
lemma tail45_checked : checkPath tail45 (-31) (3) = true :=
  checkPath_append block45 tail46 (-31) (3) (-84) (102) block45_checked tail46_checked
def tail44 : List Step := block44 ++ tail45
lemma tail44_checked : checkPath tail44 (14) (-17) = true :=
  checkPath_append block44 tail45 (14) (-17) (-31) (3) block44_checked tail45_checked
def tail43 : List Step := block43 ++ tail44
lemma tail43_checked : checkPath tail43 (14) (-17) = true :=
  checkPath_append block43 tail44 (14) (-17) (14) (-17) block43_checked tail44_checked
def tail42 : List Step := block42 ++ tail43
lemma tail42_checked : checkPath tail42 (-5) (110) = true :=
  checkPath_append block42 tail43 (-5) (110) (14) (-17) block42_checked tail43_checked
def tail41 : List Step := block41 ++ tail42
lemma tail41_checked : checkPath tail41 (68) (56) = true :=
  checkPath_append block41 tail42 (68) (56) (-5) (110) block41_checked tail42_checked
def tail40 : List Step := block40 ++ tail41
lemma tail40_checked : checkPath tail40 (14) (-17) = true :=
  checkPath_append block40 tail41 (14) (-17) (68) (56) block40_checked tail41_checked
def tail39 : List Step := block39 ++ tail40
lemma tail39_checked : checkPath tail39 (65) (25) = true :=
  checkPath_append block39 tail40 (65) (25) (14) (-17) block39_checked tail40_checked
def tail38 : List Step := block38 ++ tail39
lemma tail38_checked : checkPath tail38 (-36) (113) = true :=
  checkPath_append block38 tail39 (-36) (113) (65) (25) block38_checked tail39_checked
def tail37 : List Step := block37 ++ tail38
lemma tail37_checked : checkPath tail37 (-36) (113) = true :=
  checkPath_append block37 tail38 (-36) (113) (-36) (113) block37_checked tail38_checked
def tail36 : List Step := block36 ++ tail37
lemma tail36_checked : checkPath tail36 (-98) (119) = true :=
  checkPath_append block36 tail37 (-98) (119) (-36) (113) block36_checked tail37_checked
def tail35 : List Step := block35 ++ tail36
lemma tail35_checked : checkPath tail35 (-3) (-31) = true :=
  checkPath_append block35 tail36 (-3) (-31) (-98) (119) block35_checked tail36_checked
def tail34 : List Step := block34 ++ tail35
lemma tail34_checked : checkPath tail34 (14) (-17) = true :=
  checkPath_append block34 tail35 (14) (-17) (-3) (-31) block34_checked tail35_checked
def tail33 : List Step := block33 ++ tail34
lemma tail33_checked : checkPath tail33 (-98) (119) = true :=
  checkPath_append block33 tail34 (-98) (119) (14) (-17) block33_checked tail34_checked
def tail32 : List Step := block32 ++ tail33
lemma tail32_checked : checkPath tail32 (-98) (119) = true :=
  checkPath_append block32 tail33 (-98) (119) (-98) (119) block32_checked tail33_checked
def tail31 : List Step := block31 ++ tail32
lemma tail31_checked : checkPath tail31 (-116) (-67) = true :=
  checkPath_append block31 tail32 (-116) (-67) (-98) (119) block31_checked tail32_checked
def tail30 : List Step := block30 ++ tail31
lemma tail30_checked : checkPath tail30 (14) (-17) = true :=
  checkPath_append block30 tail31 (14) (-17) (-116) (-67) block30_checked tail31_checked
def tail29 : List Step := block29 ++ tail30
lemma tail29_checked : checkPath tail29 (-121) (43) = true :=
  checkPath_append block29 tail30 (-121) (43) (14) (-17) block29_checked tail30_checked
def tail28 : List Step := block28 ++ tail29
lemma tail28_checked : checkPath tail28 (14) (-17) = true :=
  checkPath_append block28 tail29 (14) (-17) (-121) (43) block28_checked tail29_checked
def tail27 : List Step := block27 ++ tail28
lemma tail27_checked : checkPath tail27 (-68) (-56) = true :=
  checkPath_append block27 tail28 (-68) (-56) (14) (-17) block27_checked tail28_checked
def tail26 : List Step := block26 ++ tail27
lemma tail26_checked : checkPath tail26 (-11) (48) = true :=
  checkPath_append block26 tail27 (-11) (48) (-68) (-56) block26_checked tail27_checked
def tail25 : List Step := block25 ++ tail26
lemma tail25_checked : checkPath tail25 (-11) (48) = true :=
  checkPath_append block25 tail26 (-11) (48) (-11) (48) block25_checked tail26_checked
def tail24 : List Step := block24 ++ tail25
lemma tail24_checked : checkPath tail24 (14) (-17) = true :=
  checkPath_append block24 tail25 (14) (-17) (-11) (48) block24_checked tail25_checked
def tail23 : List Step := block23 ++ tail24
lemma tail23_checked : checkPath tail23 (73) (-54) = true :=
  checkPath_append block23 tail24 (73) (-54) (14) (-17) block23_checked tail24_checked
def tail22 : List Step := block22 ++ tail23
lemma tail22_checked : checkPath tail22 (-118) (74) = true :=
  checkPath_append block22 tail23 (-118) (74) (73) (-54) block22_checked tail23_checked
def tail21 : List Step := block21 ++ tail22
lemma tail21_checked : checkPath tail21 (14) (-17) = true :=
  checkPath_append block21 tail22 (14) (-17) (-118) (74) block21_checked tail22_checked
def tail20 : List Step := block20 ++ tail21
lemma tail20_checked : checkPath tail20 (14) (-17) = true :=
  checkPath_append block20 tail21 (14) (-17) (14) (-17) block20_checked tail21_checked
def tail19 : List Step := block19 ++ tail20
lemma tail19_checked : checkPath tail19 (14) (-17) = true :=
  checkPath_append block19 tail20 (14) (-17) (14) (-17) block19_checked tail20_checked
def tail18 : List Step := block18 ++ tail19
lemma tail18_checked : checkPath tail18 (14) (-17) = true :=
  checkPath_append block18 tail19 (14) (-17) (14) (-17) block18_checked tail19_checked
def tail17 : List Step := block17 ++ tail18
lemma tail17_checked : checkPath tail17 (-68) (-56) = true :=
  checkPath_append block17 tail18 (-68) (-56) (14) (-17) block17_checked tail18_checked
def tail16 : List Step := block16 ++ tail17
lemma tail16_checked : checkPath tail16 (14) (-17) = true :=
  checkPath_append block16 tail17 (14) (-17) (-68) (-56) block16_checked tail17_checked
def tail15 : List Step := block15 ++ tail16
lemma tail15_checked : checkPath tail15 (14) (-17) = true :=
  checkPath_append block15 tail16 (14) (-17) (14) (-17) block15_checked tail16_checked
def tail14 : List Step := block14 ++ tail15
lemma tail14_checked : checkPath tail14 (-121) (43) = true :=
  checkPath_append block14 tail15 (-121) (43) (14) (-17) block14_checked tail15_checked
def tail13 : List Step := block13 ++ tail14
lemma tail13_checked : checkPath tail13 (-31) (3) = true :=
  checkPath_append block13 tail14 (-31) (3) (-121) (43) block13_checked tail14_checked
def tail12 : List Step := block12 ++ tail13
lemma tail12_checked : checkPath tail12 (-31) (3) = true :=
  checkPath_append block12 tail13 (-31) (3) (-31) (3) block12_checked tail13_checked
def tail11 : List Step := block11 ++ tail12
lemma tail11_checked : checkPath tail11 (-81) (133) = true :=
  checkPath_append block11 tail12 (-81) (133) (-31) (3) block11_checked tail12_checked
def tail10 : List Step := block10 ++ tail11
lemma tail10_checked : checkPath tail10 (-98) (119) = true :=
  checkPath_append block10 tail11 (-98) (119) (-81) (133) block10_checked tail11_checked
def tail9 : List Step := block9 ++ tail10
lemma tail9_checked : checkPath tail9 (34) (28) = true :=
  checkPath_append block9 tail10 (34) (28) (-98) (119) block9_checked tail10_checked
def tail8 : List Step := block8 ++ tail9
lemma tail8_checked : checkPath tail8 (-84) (102) = true :=
  checkPath_append block8 tail9 (-84) (102) (34) (28) block8_checked tail9_checked
def tail7 : List Step := block7 ++ tail8
lemma tail7_checked : checkPath tail7 (-84) (102) = true :=
  checkPath_append block7 tail8 (-84) (102) (-84) (102) block7_checked tail8_checked
def tail6 : List Step := block6 ++ tail7
lemma tail6_checked : checkPath tail6 (-104) (57) = true :=
  checkPath_append block6 tail7 (-104) (57) (-84) (102) block6_checked tail7_checked
def tail5 : List Step := block5 ++ tail6
lemma tail5_checked : checkPath tail5 (-118) (74) = true :=
  checkPath_append block5 tail6 (-118) (74) (-104) (57) block5_checked tail6_checked
def tail4 : List Step := block4 ++ tail5
lemma tail4_checked : checkPath tail4 (14) (-17) = true :=
  checkPath_append block4 tail5 (14) (-17) (-118) (74) block4_checked tail5_checked
def tail3 : List Step := block3 ++ tail4
lemma tail3_checked : checkPath tail3 (-87) (71) = true :=
  checkPath_append block3 tail4 (-87) (71) (14) (-17) block3_checked tail4_checked
def tail2 : List Step := block2 ++ tail3
lemma tail2_checked : checkPath tail2 (-104) (57) = true :=
  checkPath_append block2 tail3 (-104) (57) (-87) (71) block2_checked tail3_checked
def tail1 : List Step := block1 ++ tail2
lemma tail1_checked : checkPath tail1 (93) (-9) = true :=
  checkPath_append block1 tail2 (93) (-9) (-104) (57) block1_checked tail2_checked
def tail0 : List Step := block0 ++ tail1
lemma tail0_checked : checkPath tail0 (0) (0) = true :=
  checkPath_append block0 tail1 (0) (0) (93) (-9) block0_checked tail1_checked

def steps : List Step := tail0
lemma path_verified : checkPath steps 0 0 = true := tail0_checked



end Erdos773.ParametricSphere
