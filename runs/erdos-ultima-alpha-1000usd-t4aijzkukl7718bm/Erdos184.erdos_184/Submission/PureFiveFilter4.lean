import Submission.FiniteCaseLookup
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Basic

/-! Pure numerical survivor lookup for five-color pattern 4. -/
namespace Erdos184Work.PureFiveFilter4
open FiniteCaseLookup
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
def digit0 (j : ℕ) : Fin 60 := ⟨j / 20736 % 60,Nat.mod_lt _ (by decide)⟩
def digit1 (j : ℕ) : Fin 12 := ⟨j / 1728 % 12,Nat.mod_lt _ (by decide)⟩
def digit2 (j : ℕ) : Fin 12 := ⟨j / 144 % 12,Nat.mod_lt _ (by decide)⟩
def digit3 (j : ℕ) : Fin 12 := ⟨j / 12 % 12,Nat.mod_lt _ (by decide)⟩
def digit4 (j : ℕ) : Fin 12 := ⟨j / 1 % 12,Nat.mod_lt _ (by decide)⟩
def enc00 : Fin 12 → ℕ := ![1,1,1,1,1,1,1,1,1,1,1,1]
def enc01 : Fin 12 → ℕ := ![1,1,1,1,1,1,1,1,1,1,1,1]
def enc02 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
def enc03 : Fin 12 → ℕ := ![1,2,3,2,3,1,2,1,3,3,2,1]
def good0 : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,1,1,2),(1,1,1,3),(1,1,2,1),(1,1,2,3),(1,1,3,1),(1,1,3,2),(1,1,3,3)}
def compatible0 (j : ℕ) : Prop := (enc00 (digit1 j),enc01 (digit2 j),enc02 (digit3 j),enc03 (digit4 j)) ∈ good0
instance (j : ℕ) : Decidable (compatible0 j) := inferInstanceAs (Decidable (_ ∈ good0))
def enc10 : Fin 60 → ℕ := ![1,2,3,2,3,1,2,1,3,1,3,2,2,3,1,3,1,2,1,3,2,3,2,1,1,2,3,2,3,1,1,2,1,2,3,2,3,2,3,1,3,1,2,1,3,3,2,1,2,1,3,3,3,3,2,1,2,2,1,1]
def enc11 : Fin 12 → ℕ := ![3,1,2,1,2,3,3,1,3,1,2,2]
def enc12 : Fin 12 → ℕ := ![3,1,2,1,2,3,3,1,3,1,2,2]
def enc13 : Fin 12 → ℕ := ![1,2,1,1,2,2,1,2,3,3,3,3]
def good1 : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,2,2,3),(2,2,2,3),(3,1,2,3),(3,2,1,3),(3,2,2,1),(3,2,2,2),(3,2,2,3),(3,2,3,3),(3,3,2,3)}
def compatible1 (j : ℕ) : Prop := (enc10 (digit0 j),enc11 (digit3 j),enc12 (digit4 j),enc13 (digit2 j)) ∈ good1
instance (j : ℕ) : Decidable (compatible1 j) := inferInstanceAs (Decidable (_ ∈ good1))
def enc20 : Fin 60 → ℕ := ![1,2,1,1,2,2,1,2,1,1,2,2,1,1,1,1,1,1,2,2,2,2,2,2,1,2,1,1,2,2,1,2,3,3,3,3,3,2,3,3,3,1,1,2,1,2,1,2,3,3,3,3,3,3,3,3,3,3,3,3]
def enc21 : Fin 12 → ℕ := ![3,1,3,3,1,1,3,1,2,2,2,2]
def enc22 : Fin 12 → ℕ := ![3,1,3,3,1,1,3,1,2,2,2,2]
def enc23 : Fin 12 → ℕ := ![1,2,1,1,2,2,1,2,3,3,3,3]
def good2 : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,2,2,3),(2,2,2,3),(3,1,2,3),(3,2,1,3),(3,2,2,1),(3,2,2,2),(3,2,2,3),(3,2,3,3),(3,3,2,3)}
def compatible2 (j : ℕ) : Prop := (enc20 (digit0 j),enc21 (digit3 j),enc22 (digit4 j),enc23 (digit1 j)) ∈ good2
instance (j : ℕ) : Decidable (compatible2 j) := inferInstanceAs (Decidable (_ ∈ good2))
def enc30 : Fin 12 → ℕ := ![1,1,1,1,1,1,1,1,1,1,1,1]
def enc31 : Fin 12 → ℕ := ![2,2,2,1,1,1,3,3,3,1,2,3]
def enc32 : Fin 12 → ℕ := ![2,2,2,1,1,1,3,3,3,1,2,3]
def enc33 : Fin 60 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,3,3,3,0,0,0,0,1,3,0,4,4,4,0,4,2,2,2,4,0,0,0,0,2,0,3,0,0,0,1,0,2,0]
def good3 : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,1,1,2),(1,1,2,1),(1,1,3,1),(1,1,3,2),(1,2,1,4),(1,2,2,3),(1,2,3,3),(1,2,3,4),(1,3,1,2),(1,3,1,4),(1,3,2,1),(1,3,2,3)}
def compatible3 (j : ℕ) : Prop := (enc30 (digit4 j),enc31 (digit1 j),enc32 (digit2 j),enc33 (digit0 j)) ∈ good3
instance (j : ℕ) : Decidable (compatible3 j) := inferInstanceAs (Decidable (_ ∈ good3))
def enc40 : Fin 12 → ℕ := ![1,1,1,1,1,1,1,1,1,1,1,1]
def enc41 : Fin 12 → ℕ := ![2,2,1,1,2,1,3,3,1,3,3,2]
def enc42 : Fin 12 → ℕ := ![2,2,1,1,2,1,3,3,1,3,3,2]
def enc43 : Fin 60 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,3,3,1,3,0,0,0,0,4,4,0,4,1,3,0,4,2,2,4,2,0,0,0,0,3,0,2,0,0,0,2,0,1,0]
def good4 : Finset (ℕ × ℕ × ℕ × ℕ) := {(1,1,1,2),(1,1,2,1),(1,1,3,1),(1,1,3,2),(1,2,1,4),(1,2,2,3),(1,2,3,3),(1,2,3,4),(1,3,1,2),(1,3,1,4),(1,3,2,1),(1,3,2,3)}
def compatible4 (j : ℕ) : Prop := (enc40 (digit3 j),enc41 (digit1 j),enc42 (digit2 j),enc43 (digit0 j)) ∈ good4
instance (j : ℕ) : Decidable (compatible4 j) := inferInstanceAs (Decidable (_ ∈ good4))
def Compatible (j : ℕ) : Prop := compatible0 j ∧ compatible1 j ∧ compatible2 j ∧ compatible3 j ∧ compatible4 j
instance (j : ℕ) : Decidable (Compatible j) := by unfold Compatible; infer_instance

abbrev Cases := Fin 760
def caseKey (i : Cases) : ℕ := (if i.val < 380 then (if i.val < 190 then (if i.val < 95 then (if i.val < 47 then (if i.val < 23 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 513059 else 513070) else (if i.val < 3 then 514931 else (if i.val < 4 then 514942 else 533795))) else (if i.val < 8 then (if i.val < 6 then 533806 else (if i.val < 7 then 535667 else 535678)) else (if i.val < 9 then 554819 else (if i.val < 10 then 554830 else 554963)))) else (if i.val < 17 then (if i.val < 14 then (if i.val < 12 then 554974 else (if i.val < 13 then 556378 else 556379)) else (if i.val < 15 then 556390 else (if i.val < 16 then 556391 else 556400))) else (if i.val < 20 then (if i.val < 18 then 556401 else (if i.val < 19 then 556403 else 556412)) else (if i.val < 21 then 556413 else (if i.val < 22 then 556414 else 558275))))) else (if i.val < 35 then (if i.val < 29 then (if i.val < 26 then (if i.val < 24 then 558286 else (if i.val < 25 then 558419 else 558430)) else (if i.val < 27 then 559690 else (if i.val < 28 then 559691 else 559702))) else (if i.val < 32 then (if i.val < 30 then 559703 else (if i.val < 31 then 559712 else 559713)) else (if i.val < 33 then 559715 else (if i.val < 34 then 559724 else 559725)))) else (if i.val < 41 then (if i.val < 38 then (if i.val < 36 then 559726 else (if i.val < 37 then 578867 else 578878)) else (if i.val < 39 then 580451 else (if i.val < 40 then 580462 else 594563))) else (if i.val < 44 then (if i.val < 42 then 594574 else (if i.val < 43 then 594707 else 594718)) else (if i.val < 45 then 595978 else (if i.val < 46 then 595979 else 595990)))))) else (if i.val < 71 then (if i.val < 59 then (if i.val < 53 then (if i.val < 50 then (if i.val < 48 then 595991 else (if i.val < 49 then 596000 else 596001)) else (if i.val < 51 then 596003 else (if i.val < 52 then 596012 else 596013))) else (if i.val < 56 then (if i.val < 54 then 596014 else (if i.val < 55 then 598019 else 598030)) else (if i.val < 57 then 598163 else (if i.val < 58 then 598174 else 599578)))) else (if i.val < 65 then (if i.val < 62 then (if i.val < 60 then 599579 else (if i.val < 61 then 599590 else 599591)) else (if i.val < 63 then 599600 else (if i.val < 64 then 599601 else 599603))) else (if i.val < 68 then (if i.val < 66 then 599612 else (if i.val < 67 then 599613 else 599614)) else (if i.val < 69 then 620339 else (if i.val < 70 then 620350 else 621923))))) else (if i.val < 83 then (if i.val < 77 then (if i.val < 74 then (if i.val < 72 then 621934 else (if i.val < 73 then 712355 else 712366)) else (if i.val < 75 then 712931 else (if i.val < 76 then 712942 else 713075))) else (if i.val < 80 then (if i.val < 78 then 713086 else (if i.val < 79 then 713194 else 713195)) else (if i.val < 81 then 713206 else (if i.val < 82 then 713207 else 713216)))) else (if i.val < 89 then (if i.val < 86 then (if i.val < 84 then 713217 else (if i.val < 85 then 713219 else 713228)) else (if i.val < 87 then 713229 else (if i.val < 88 then 713230 else 713482))) else (if i.val < 92 then (if i.val < 90 then 713483 else (if i.val < 91 then 713494 else 713495)) else (if i.val < 93 then 713504 else (if i.val < 94 then 713505 else 713507))))))) else (if i.val < 142 then (if i.val < 118 then (if i.val < 106 then (if i.val < 100 then (if i.val < 97 then (if i.val < 96 then 713516 else 713517) else (if i.val < 98 then 713518 else (if i.val < 99 then 715811 else 715822))) else (if i.val < 103 then (if i.val < 101 then 717539 else (if i.val < 102 then 717550 else 720898)) else (if i.val < 104 then 720899 else (if i.val < 105 then 720922 else 720923)))) else (if i.val < 112 then (if i.val < 109 then (if i.val < 107 then 720986 else (if i.val < 108 then 720988 else 720995)) else (if i.val < 110 then 720998 else (if i.val < 111 then 721000 else 721006))) else (if i.val < 115 then (if i.val < 113 then 721738 else (if i.val < 114 then 721751 else 721760)) else (if i.val < 116 then 721761 else (if i.val < 117 then 721762 else 721763))))) else (if i.val < 130 then (if i.val < 124 then (if i.val < 121 then (if i.val < 119 then 721775 else (if i.val < 120 then 721784 else 721785)) else (if i.val < 122 then 721786 else (if i.val < 123 then 721787 else 721798))) else (if i.val < 127 then (if i.val < 125 then 721811 else (if i.val < 126 then 721822 else 721826)) else (if i.val < 128 then 721828 else (if i.val < 129 then 721834 else 721835)))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 131 then 721838 else (if i.val < 132 then 721840 else 721846)) else (if i.val < 134 then 721847 else (if i.val < 135 then 721848 else 721850))) else (if i.val < 139 then (if i.val < 137 then 721852 else (if i.val < 138 then 721853 else 721855)) else (if i.val < 140 then 721856 else (if i.val < 141 then 721857 else 721859)))))) else (if i.val < 166 then (if i.val < 154 then (if i.val < 148 then (if i.val < 145 then (if i.val < 143 then 721861 else (if i.val < 144 then 721862 else 721863)) else (if i.val < 146 then 721864 else (if i.val < 147 then 721866 else 721868))) else (if i.val < 151 then (if i.val < 149 then 721869 else (if i.val < 150 then 721870 else 724354)) else (if i.val < 152 then 724355 else (if i.val < 153 then 724378 else 724379)))) else (if i.val < 160 then (if i.val < 157 then (if i.val < 155 then 724442 else (if i.val < 156 then 724444 else 724451)) else (if i.val < 158 then 724454 else (if i.val < 159 then 724456 else 724462))) else (if i.val < 163 then (if i.val < 161 then 725482 else (if i.val < 162 then 725495 else 725504)) else (if i.val < 164 then 725505 else (if i.val < 165 then 725506 else 725507))))) else (if i.val < 178 then (if i.val < 172 then (if i.val < 169 then (if i.val < 167 then 725519 else (if i.val < 168 then 725528 else 725529)) else (if i.val < 170 then 725530 else (if i.val < 171 then 725531 else 725542))) else (if i.val < 175 then (if i.val < 173 then 725555 else (if i.val < 174 then 725566 else 725570)) else (if i.val < 176 then 725572 else (if i.val < 177 then 725578 else 725579)))) else (if i.val < 184 then (if i.val < 181 then (if i.val < 179 then 725582 else (if i.val < 180 then 725584 else 725590)) else (if i.val < 182 then 725591 else (if i.val < 183 then 725592 else 725594))) else (if i.val < 187 then (if i.val < 185 then 725596 else (if i.val < 186 then 725597 else 725599)) else (if i.val < 188 then 725600 else (if i.val < 189 then 725601 else 725603)))))))) else (if i.val < 285 then (if i.val < 237 then (if i.val < 213 then (if i.val < 201 then (if i.val < 195 then (if i.val < 192 then (if i.val < 191 then 725605 else 725606) else (if i.val < 193 then 725607 else (if i.val < 194 then 725608 else 725610))) else (if i.val < 198 then (if i.val < 196 then 725612 else (if i.val < 197 then 725613 else 725614)) else (if i.val < 199 then 727043 else (if i.val < 200 then 727054 else 727331)))) else (if i.val < 207 then (if i.val < 204 then (if i.val < 202 then 727342 else (if i.val < 203 then 728771 else 728782)) else (if i.val < 205 then 729059 else (if i.val < 206 then 729070 else 744226))) else (if i.val < 210 then (if i.val < 208 then 744227 else (if i.val < 209 then 744250 else 744251)) else (if i.val < 211 then 744314 else (if i.val < 212 then 744316 else 744323))))) else (if i.val < 225 then (if i.val < 219 then (if i.val < 216 then (if i.val < 214 then 744326 else (if i.val < 215 then 744328 else 744334)) else (if i.val < 217 then 746242 else (if i.val < 218 then 746243 else 746266))) else (if i.val < 222 then (if i.val < 220 then 746267 else (if i.val < 221 then 746330 else 746332)) else (if i.val < 223 then 746339 else (if i.val < 224 then 746342 else 746344)))) else (if i.val < 231 then (if i.val < 228 then (if i.val < 226 then 746350 else (if i.val < 227 then 785795 else 785806)) else (if i.val < 229 then 787667 else (if i.val < 230 then 787678 else 792131))) else (if i.val < 234 then (if i.val < 232 then 792142 else (if i.val < 233 then 792419 else 792430)) else (if i.val < 235 then 792563 else (if i.val < 236 then 792574 else 792826)))))) else (if i.val < 261 then (if i.val < 249 then (if i.val < 243 then (if i.val < 240 then (if i.val < 238 then 792827 else (if i.val < 239 then 792838 else 792839)) else (if i.val < 241 then 792848 else (if i.val < 242 then 792849 else 792851))) else (if i.val < 246 then (if i.val < 244 then 792860 else (if i.val < 245 then 792861 else 792862)) else (if i.val < 247 then 793114 else (if i.val < 248 then 793115 else 793126)))) else (if i.val < 255 then (if i.val < 252 then (if i.val < 250 then 793127 else (if i.val < 251 then 793136 else 793137)) else (if i.val < 253 then 793139 else (if i.val < 254 then 793148 else 793149))) else (if i.val < 258 then (if i.val < 256 then 793150 else (if i.val < 257 then 799043 else 799054)) else (if i.val < 259 then 800771 else (if i.val < 260 then 800782 else 802402))))) else (if i.val < 273 then (if i.val < 267 then (if i.val < 264 then (if i.val < 262 then 802403 else (if i.val < 263 then 802426 else 802427)) else (if i.val < 265 then 802490 else (if i.val < 266 then 802492 else 802499))) else (if i.val < 270 then (if i.val < 268 then 802502 else (if i.val < 269 then 802504 else 802510)) else (if i.val < 271 then 803098 else (if i.val < 272 then 803111 else 803120)))) else (if i.val < 279 then (if i.val < 276 then (if i.val < 274 then 803121 else (if i.val < 275 then 803122 else 803123)) else (if i.val < 277 then 803135 else (if i.val < 278 then 803144 else 803145))) else (if i.val < 282 then (if i.val < 280 then 803146 else (if i.val < 281 then 803147 else 803158)) else (if i.val < 283 then 803171 else (if i.val < 284 then 803182 else 803186))))))) else (if i.val < 332 then (if i.val < 308 then (if i.val < 296 then (if i.val < 290 then (if i.val < 287 then (if i.val < 286 then 803188 else 803194) else (if i.val < 288 then 803195 else (if i.val < 289 then 803198 else 803200))) else (if i.val < 293 then (if i.val < 291 then 803206 else (if i.val < 292 then 803207 else 803208)) else (if i.val < 294 then 803210 else (if i.val < 295 then 803212 else 803213)))) else (if i.val < 302 then (if i.val < 299 then (if i.val < 297 then 803215 else (if i.val < 298 then 803216 else 803217)) else (if i.val < 300 then 803219 else (if i.val < 301 then 803221 else 803222))) else (if i.val < 305 then (if i.val < 303 then 803223 else (if i.val < 304 then 803224 else 803226)) else (if i.val < 306 then 803228 else (if i.val < 307 then 803229 else 803230))))) else (if i.val < 320 then (if i.val < 314 then (if i.val < 311 then (if i.val < 309 then 805858 else (if i.val < 310 then 805859 else 805882)) else (if i.val < 312 then 805883 else (if i.val < 313 then 805946 else 805948))) else (if i.val < 317 then (if i.val < 315 then 805955 else (if i.val < 316 then 805958 else 805960)) else (if i.val < 318 then 805966 else (if i.val < 319 then 806842 else 806855)))) else (if i.val < 326 then (if i.val < 323 then (if i.val < 321 then 806864 else (if i.val < 322 then 806865 else 806866)) else (if i.val < 324 then 806867 else (if i.val < 325 then 806879 else 806888))) else (if i.val < 329 then (if i.val < 327 then 806889 else (if i.val < 328 then 806890 else 806891)) else (if i.val < 330 then 806902 else (if i.val < 331 then 806915 else 806926)))))) else (if i.val < 356 then (if i.val < 344 then (if i.val < 338 then (if i.val < 335 then (if i.val < 333 then 806930 else (if i.val < 334 then 806932 else 806938)) else (if i.val < 336 then 806939 else (if i.val < 337 then 806942 else 806944))) else (if i.val < 341 then (if i.val < 339 then 806950 else (if i.val < 340 then 806951 else 806952)) else (if i.val < 342 then 806954 else (if i.val < 343 then 806956 else 806957)))) else (if i.val < 350 then (if i.val < 347 then (if i.val < 345 then 806959 else (if i.val < 346 then 806960 else 806961)) else (if i.val < 348 then 806963 else (if i.val < 349 then 806965 else 806966))) else (if i.val < 353 then (if i.val < 351 then 806967 else (if i.val < 352 then 806968 else 806970)) else (if i.val < 354 then 806972 else (if i.val < 355 then 806973 else 806974))))) else (if i.val < 368 then (if i.val < 362 then (if i.val < 359 then (if i.val < 357 then 810131 else (if i.val < 358 then 810142 else 810419)) else (if i.val < 360 then 810430 else (if i.val < 361 then 811859 else 811870))) else (if i.val < 365 then (if i.val < 363 then 812147 else (if i.val < 364 then 812158 else 827602)) else (if i.val < 366 then 827603 else (if i.val < 367 then 827626 else 827627)))) else (if i.val < 374 then (if i.val < 371 then (if i.val < 369 then 827690 else (if i.val < 370 then 827692 else 827699)) else (if i.val < 372 then 827702 else (if i.val < 373 then 827704 else 827710))) else (if i.val < 377 then (if i.val < 375 then 829042 else (if i.val < 376 then 829043 else 829066)) else (if i.val < 378 then 829067 else (if i.val < 379 then 829130 else 829132))))))))) else (if i.val < 570 then (if i.val < 475 then (if i.val < 427 then (if i.val < 403 then (if i.val < 391 then (if i.val < 385 then (if i.val < 382 then (if i.val < 381 then 829139 else 829142) else (if i.val < 383 then 829144 else (if i.val < 384 then 829150 else 868739))) else (if i.val < 388 then (if i.val < 386 then 868750 else (if i.val < 387 then 870611 else 870622)) else (if i.val < 389 then 886163 else (if i.val < 390 then 886174 else 887747)))) else (if i.val < 397 then (if i.val < 394 then (if i.val < 392 then 887758 else (if i.val < 393 then 906899 else 906910)) else (if i.val < 395 then 908483 else (if i.val < 396 then 908494 else 928499))) else (if i.val < 400 then (if i.val < 398 then 928510 else (if i.val < 399 then 928787 else 928798)) else (if i.val < 401 then 929194 else (if i.val < 402 then 929195 else 929206))))) else (if i.val < 415 then (if i.val < 409 then (if i.val < 406 then (if i.val < 404 then 929207 else (if i.val < 405 then 929216 else 929217)) else (if i.val < 407 then 929219 else (if i.val < 408 then 929228 else 929229))) else (if i.val < 412 then (if i.val < 410 then 929230 else (if i.val < 411 then 931955 else 931966)) else (if i.val < 413 then 932243 else (if i.val < 414 then 932254 else 932794)))) else (if i.val < 421 then (if i.val < 418 then (if i.val < 416 then 932795 else (if i.val < 417 then 932806 else 932807)) else (if i.val < 419 then 932816 else (if i.val < 420 then 932817 else 932819))) else (if i.val < 424 then (if i.val < 422 then 932828 else (if i.val < 423 then 932829 else 932830)) else (if i.val < 425 then 947507 else (if i.val < 426 then 947518 else 947795)))))) else (if i.val < 451 then (if i.val < 439 then (if i.val < 433 then (if i.val < 430 then (if i.val < 428 then 947806 else (if i.val < 429 then 948346 else 948347)) else (if i.val < 431 then 948358 else (if i.val < 432 then 948359 else 948368))) else (if i.val < 436 then (if i.val < 434 then 948369 else (if i.val < 435 then 948371 else 948380)) else (if i.val < 437 then 948381 else (if i.val < 438 then 948382 else 950963)))) else (if i.val < 445 then (if i.val < 442 then (if i.val < 440 then 950974 else (if i.val < 441 then 951251 else 951262)) else (if i.val < 443 then 951658 else (if i.val < 444 then 951659 else 951670))) else (if i.val < 448 then (if i.val < 446 then 951671 else (if i.val < 447 then 951680 else 951681)) else (if i.val < 449 then 951683 else (if i.val < 450 then 951692 else 951693))))) else (if i.val < 463 then (if i.val < 457 then (if i.val < 454 then (if i.val < 452 then 951694 else (if i.val < 453 then 1044419 else 1044430)) else (if i.val < 455 then 1044707 else (if i.val < 456 then 1044718 else 1044851))) else (if i.val < 460 then (if i.val < 458 then 1044862 else (if i.val < 459 then 1045114 else 1045115)) else (if i.val < 461 then 1045126 else (if i.val < 462 then 1045127 else 1045136)))) else (if i.val < 469 then (if i.val < 466 then (if i.val < 464 then 1045137 else (if i.val < 465 then 1045139 else 1045148)) else (if i.val < 467 then 1045149 else (if i.val < 468 then 1045150 else 1045402))) else (if i.val < 472 then (if i.val < 470 then 1045403 else (if i.val < 471 then 1045414 else 1045415)) else (if i.val < 473 then 1045424 else (if i.val < 474 then 1045425 else 1045427))))))) else (if i.val < 522 then (if i.val < 498 then (if i.val < 486 then (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then 1045436 else 1045437) else (if i.val < 478 then 1045438 else (if i.val < 479 then 1047875 else 1047886))) else (if i.val < 483 then (if i.val < 481 then 1049603 else (if i.val < 482 then 1049614 else 1052962)) else (if i.val < 484 then 1052963 else (if i.val < 485 then 1052986 else 1052987)))) else (if i.val < 492 then (if i.val < 489 then (if i.val < 487 then 1053050 else (if i.val < 488 then 1053052 else 1053059)) else (if i.val < 490 then 1053062 else (if i.val < 491 then 1053064 else 1053070))) else (if i.val < 495 then (if i.val < 493 then 1053946 else (if i.val < 494 then 1053959 else 1053968)) else (if i.val < 496 then 1053969 else (if i.val < 497 then 1053970 else 1053971))))) else (if i.val < 510 then (if i.val < 504 then (if i.val < 501 then (if i.val < 499 then 1053983 else (if i.val < 500 then 1053992 else 1053993)) else (if i.val < 502 then 1053994 else (if i.val < 503 then 1053995 else 1054006))) else (if i.val < 507 then (if i.val < 505 then 1054019 else (if i.val < 506 then 1054030 else 1054034)) else (if i.val < 508 then 1054036 else (if i.val < 509 then 1054042 else 1054043)))) else (if i.val < 516 then (if i.val < 513 then (if i.val < 511 then 1054046 else (if i.val < 512 then 1054048 else 1054054)) else (if i.val < 514 then 1054055 else (if i.val < 515 then 1054056 else 1054058))) else (if i.val < 519 then (if i.val < 517 then 1054060 else (if i.val < 518 then 1054061 else 1054063)) else (if i.val < 520 then 1054064 else (if i.val < 521 then 1054065 else 1054067)))))) else (if i.val < 546 then (if i.val < 534 then (if i.val < 528 then (if i.val < 525 then (if i.val < 523 then 1054069 else (if i.val < 524 then 1054070 else 1054071)) else (if i.val < 526 then 1054072 else (if i.val < 527 then 1054074 else 1054076))) else (if i.val < 531 then (if i.val < 529 then 1054077 else (if i.val < 530 then 1054078 else 1056418)) else (if i.val < 532 then 1056419 else (if i.val < 533 then 1056442 else 1056443)))) else (if i.val < 540 then (if i.val < 537 then (if i.val < 535 then 1056506 else (if i.val < 536 then 1056508 else 1056515)) else (if i.val < 538 then 1056518 else (if i.val < 539 then 1056520 else 1056526))) else (if i.val < 543 then (if i.val < 541 then 1057114 else (if i.val < 542 then 1057127 else 1057136)) else (if i.val < 544 then 1057137 else (if i.val < 545 then 1057138 else 1057139))))) else (if i.val < 558 then (if i.val < 552 then (if i.val < 549 then (if i.val < 547 then 1057151 else (if i.val < 548 then 1057160 else 1057161)) else (if i.val < 550 then 1057162 else (if i.val < 551 then 1057163 else 1057174))) else (if i.val < 555 then (if i.val < 553 then 1057187 else (if i.val < 554 then 1057198 else 1057202)) else (if i.val < 556 then 1057204 else (if i.val < 557 then 1057210 else 1057211)))) else (if i.val < 564 then (if i.val < 561 then (if i.val < 559 then 1057214 else (if i.val < 560 then 1057216 else 1057222)) else (if i.val < 562 then 1057223 else (if i.val < 563 then 1057224 else 1057226))) else (if i.val < 567 then (if i.val < 565 then 1057228 else (if i.val < 566 then 1057229 else 1057231)) else (if i.val < 568 then 1057232 else (if i.val < 569 then 1057233 else 1057235)))))))) else (if i.val < 665 then (if i.val < 617 then (if i.val < 593 then (if i.val < 581 then (if i.val < 575 then (if i.val < 572 then (if i.val < 571 then 1057237 else 1057238) else (if i.val < 573 then 1057239 else (if i.val < 574 then 1057240 else 1057242))) else (if i.val < 578 then (if i.val < 576 then 1057244 else (if i.val < 577 then 1057245 else 1057246)) else (if i.val < 579 then 1082147 else (if i.val < 580 then 1082158 else 1082723)))) else (if i.val < 587 then (if i.val < 584 then (if i.val < 582 then 1082734 else (if i.val < 583 then 1082867 else 1082878)) else (if i.val < 585 then 1082986 else (if i.val < 586 then 1082987 else 1082998))) else (if i.val < 590 then (if i.val < 588 then 1082999 else (if i.val < 589 then 1083008 else 1083009)) else (if i.val < 591 then 1083011 else (if i.val < 592 then 1083020 else 1083021))))) else (if i.val < 605 then (if i.val < 599 then (if i.val < 596 then (if i.val < 594 then 1083022 else (if i.val < 595 then 1083274 else 1083275)) else (if i.val < 597 then 1083286 else (if i.val < 598 then 1083287 else 1083296))) else (if i.val < 602 then (if i.val < 600 then 1083297 else (if i.val < 601 then 1083299 else 1083308)) else (if i.val < 603 then 1083309 else (if i.val < 604 then 1083310 else 1089059)))) else (if i.val < 611 then (if i.val < 608 then (if i.val < 606 then 1089070 else (if i.val < 607 then 1090787 else 1090798)) else (if i.val < 609 then 1092418 else (if i.val < 610 then 1092419 else 1092442))) else (if i.val < 614 then (if i.val < 612 then 1092443 else (if i.val < 613 then 1092506 else 1092508)) else (if i.val < 615 then 1092515 else (if i.val < 616 then 1092518 else 1092520)))))) else (if i.val < 641 then (if i.val < 629 then (if i.val < 623 then (if i.val < 620 then (if i.val < 618 then 1092526 else (if i.val < 619 then 1093546 else 1093559)) else (if i.val < 621 then 1093568 else (if i.val < 622 then 1093569 else 1093570))) else (if i.val < 626 then (if i.val < 624 then 1093571 else (if i.val < 625 then 1093583 else 1093592)) else (if i.val < 627 then 1093593 else (if i.val < 628 then 1093594 else 1093595)))) else (if i.val < 635 then (if i.val < 632 then (if i.val < 630 then 1093606 else (if i.val < 631 then 1093619 else 1093630)) else (if i.val < 633 then 1093634 else (if i.val < 634 then 1093636 else 1093642))) else (if i.val < 638 then (if i.val < 636 then 1093643 else (if i.val < 637 then 1093646 else 1093648)) else (if i.val < 639 then 1093654 else (if i.val < 640 then 1093655 else 1093656))))) else (if i.val < 653 then (if i.val < 647 then (if i.val < 644 then (if i.val < 642 then 1093658 else (if i.val < 643 then 1093660 else 1093661)) else (if i.val < 645 then 1093663 else (if i.val < 646 then 1093664 else 1093665))) else (if i.val < 650 then (if i.val < 648 then 1093667 else (if i.val < 649 then 1093669 else 1093670)) else (if i.val < 651 then 1093671 else (if i.val < 652 then 1093672 else 1093674)))) else (if i.val < 659 then (if i.val < 656 then (if i.val < 654 then 1093676 else (if i.val < 655 then 1093677 else 1093678)) else (if i.val < 657 then 1095874 else (if i.val < 658 then 1095875 else 1095898))) else (if i.val < 662 then (if i.val < 660 then 1095899 else (if i.val < 661 then 1095962 else 1095964)) else (if i.val < 663 then 1095971 else (if i.val < 664 then 1095974 else 1095976))))))) else (if i.val < 712 then (if i.val < 688 then (if i.val < 676 then (if i.val < 670 then (if i.val < 667 then (if i.val < 666 then 1095982 else 1096714) else (if i.val < 668 then 1096727 else (if i.val < 669 then 1096736 else 1096737))) else (if i.val < 673 then (if i.val < 671 then 1096738 else (if i.val < 672 then 1096739 else 1096751)) else (if i.val < 674 then 1096760 else (if i.val < 675 then 1096761 else 1096762)))) else (if i.val < 682 then (if i.val < 679 then (if i.val < 677 then 1096763 else (if i.val < 678 then 1096774 else 1096787)) else (if i.val < 680 then 1096798 else (if i.val < 681 then 1096802 else 1096804))) else (if i.val < 685 then (if i.val < 683 then 1096810 else (if i.val < 684 then 1096811 else 1096814)) else (if i.val < 686 then 1096816 else (if i.val < 687 then 1096822 else 1096823))))) else (if i.val < 700 then (if i.val < 694 then (if i.val < 691 then (if i.val < 689 then 1096824 else (if i.val < 690 then 1096826 else 1096828)) else (if i.val < 692 then 1096829 else (if i.val < 693 then 1096831 else 1096832))) else (if i.val < 697 then (if i.val < 695 then 1096833 else (if i.val < 696 then 1096835 else 1096837)) else (if i.val < 698 then 1096838 else (if i.val < 699 then 1096839 else 1096840)))) else (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then 1096842 else (if i.val < 702 then 1096844 else 1096845)) else (if i.val < 704 then 1096846 else (if i.val < 705 then 1167683 else 1167694))) else (if i.val < 709 then (if i.val < 707 then 1167971 else (if i.val < 708 then 1167982 else 1171139)) else (if i.val < 710 then 1171150 else (if i.val < 711 then 1171427 else 1171438)))))) else (if i.val < 736 then (if i.val < 724 then (if i.val < 718 then (if i.val < 715 then (if i.val < 713 then 1176514 else (if i.val < 714 then 1176515 else 1176538)) else (if i.val < 716 then 1176539 else (if i.val < 717 then 1176602 else 1176604))) else (if i.val < 721 then (if i.val < 719 then 1176611 else (if i.val < 720 then 1176614 else 1176616)) else (if i.val < 722 then 1176622 else (if i.val < 723 then 1177954 else 1177955)))) else (if i.val < 730 then (if i.val < 727 then (if i.val < 725 then 1177978 else (if i.val < 726 then 1177979 else 1178042)) else (if i.val < 728 then 1178044 else (if i.val < 729 then 1178051 else 1178054))) else (if i.val < 733 then (if i.val < 731 then 1178056 else (if i.val < 732 then 1178062 else 1209299)) else (if i.val < 734 then 1209310 else (if i.val < 735 then 1209587 else 1209598))))) else (if i.val < 748 then (if i.val < 742 then (if i.val < 739 then (if i.val < 737 then 1212755 else (if i.val < 738 then 1212766 else 1213043)) else (if i.val < 740 then 1213054 else (if i.val < 741 then 1217842 else 1217843))) else (if i.val < 745 then (if i.val < 743 then 1217866 else (if i.val < 744 then 1217867 else 1217930)) else (if i.val < 746 then 1217932 else (if i.val < 747 then 1217939 else 1217942)))) else (if i.val < 754 then (if i.val < 751 then (if i.val < 749 then 1217944 else (if i.val < 750 then 1217950 else 1219858)) else (if i.val < 752 then 1219859 else (if i.val < 753 then 1219882 else 1219883))) else (if i.val < 757 then (if i.val < 755 then 1219946 else (if i.val < 756 then 1219948 else 1219955)) else (if i.val < 758 then 1219958 else (if i.val < 759 then 1219960 else 1219966))))))))))
def table : Table Cases :=
  (.branch 829139
 (.branch 725605
 (.branch 713516
 (.branch 595991
 (.branch 558286
 (.branch 554974
 (.branch 533806
 (.branch 514931
 (.branch 513070
 (.entry 513059 0)
 (.entry 513070 1))
 (.branch 514942
 (.entry 514931 2)
 (.branch 533795
 (.entry 514942 3)
 (.entry 533795 4))))
 (.branch 554819
 (.branch 535667
 (.entry 533806 5)
 (.branch 535678
 (.entry 535667 6)
 (.entry 535678 7)))
 (.branch 554830
 (.entry 554819 8)
 (.branch 554963
 (.entry 554830 9)
 (.entry 554963 10)))))
 (.branch 556401
 (.branch 556390
 (.branch 556378
 (.entry 554974 11)
 (.branch 556379
 (.entry 556378 12)
 (.entry 556379 13)))
 (.branch 556391
 (.entry 556390 14)
 (.branch 556400
 (.entry 556391 15)
 (.entry 556400 16))))
 (.branch 556413
 (.branch 556403
 (.entry 556401 17)
 (.branch 556412
 (.entry 556403 18)
 (.entry 556412 19)))
 (.branch 556414
 (.entry 556413 20)
 (.branch 558275
 (.entry 556414 21)
 (.entry 558275 22))))))
 (.branch 559726
 (.branch 559703
 (.branch 559690
 (.branch 558419
 (.entry 558286 23)
 (.branch 558430
 (.entry 558419 24)
 (.entry 558430 25)))
 (.branch 559691
 (.entry 559690 26)
 (.branch 559702
 (.entry 559691 27)
 (.entry 559702 28))))
 (.branch 559715
 (.branch 559712
 (.entry 559703 29)
 (.branch 559713
 (.entry 559712 30)
 (.entry 559713 31)))
 (.branch 559724
 (.entry 559715 32)
 (.branch 559725
 (.entry 559724 33)
 (.entry 559725 34)))))
 (.branch 594574
 (.branch 580451
 (.branch 578867
 (.entry 559726 35)
 (.branch 578878
 (.entry 578867 36)
 (.entry 578878 37)))
 (.branch 580462
 (.entry 580451 38)
 (.branch 594563
 (.entry 580462 39)
 (.entry 594563 40))))
 (.branch 595978
 (.branch 594707
 (.entry 594574 41)
 (.branch 594718
 (.entry 594707 42)
 (.entry 594718 43)))
 (.branch 595979
 (.entry 595978 44)
 (.branch 595990
 (.entry 595979 45)
 (.entry 595990 46)))))))
 (.branch 621934
 (.branch 599579
 (.branch 596014
 (.branch 596003
 (.branch 596000
 (.entry 595991 47)
 (.branch 596001
 (.entry 596000 48)
 (.entry 596001 49)))
 (.branch 596012
 (.entry 596003 50)
 (.branch 596013
 (.entry 596012 51)
 (.entry 596013 52))))
 (.branch 598163
 (.branch 598019
 (.entry 596014 53)
 (.branch 598030
 (.entry 598019 54)
 (.entry 598030 55)))
 (.branch 598174
 (.entry 598163 56)
 (.branch 599578
 (.entry 598174 57)
 (.entry 599578 58)))))
 (.branch 599612
 (.branch 599600
 (.branch 599590
 (.entry 599579 59)
 (.branch 599591
 (.entry 599590 60)
 (.entry 599591 61)))
 (.branch 599601
 (.entry 599600 62)
 (.branch 599603
 (.entry 599601 63)
 (.entry 599603 64))))
 (.branch 620339
 (.branch 599613
 (.entry 599612 65)
 (.branch 599614
 (.entry 599613 66)
 (.entry 599614 67)))
 (.branch 620350
 (.entry 620339 68)
 (.branch 621923
 (.entry 620350 69)
 (.entry 621923 70))))))
 (.branch 713217
 (.branch 713086
 (.branch 712931
 (.branch 712355
 (.entry 621934 71)
 (.branch 712366
 (.entry 712355 72)
 (.entry 712366 73)))
 (.branch 712942
 (.entry 712931 74)
 (.branch 713075
 (.entry 712942 75)
 (.entry 713075 76))))
 (.branch 713206
 (.branch 713194
 (.entry 713086 77)
 (.branch 713195
 (.entry 713194 78)
 (.entry 713195 79)))
 (.branch 713207
 (.entry 713206 80)
 (.branch 713216
 (.entry 713207 81)
 (.entry 713216 82)))))
 (.branch 713483
 (.branch 713229
 (.branch 713219
 (.entry 713217 83)
 (.branch 713228
 (.entry 713219 84)
 (.entry 713228 85)))
 (.branch 713230
 (.entry 713229 86)
 (.branch 713482
 (.entry 713230 87)
 (.entry 713482 88))))
 (.branch 713504
 (.branch 713494
 (.entry 713483 89)
 (.branch 713495
 (.entry 713494 90)
 (.entry 713495 91)))
 (.branch 713505
 (.entry 713504 92)
 (.branch 713507
 (.entry 713505 93)
 (.entry 713507 94))))))))
 (.branch 721861
 (.branch 721775
 (.branch 720986
 (.branch 717539
 (.branch 713518
 (.branch 713517
 (.entry 713516 95)
 (.entry 713517 96))
 (.branch 715811
 (.entry 713518 97)
 (.branch 715822
 (.entry 715811 98)
 (.entry 715822 99))))
 (.branch 720899
 (.branch 717550
 (.entry 717539 100)
 (.branch 720898
 (.entry 717550 101)
 (.entry 720898 102)))
 (.branch 720922
 (.entry 720899 103)
 (.branch 720923
 (.entry 720922 104)
 (.entry 720923 105)))))
 (.branch 721738
 (.branch 720998
 (.branch 720988
 (.entry 720986 106)
 (.branch 720995
 (.entry 720988 107)
 (.entry 720995 108)))
 (.branch 721000
 (.entry 720998 109)
 (.branch 721006
 (.entry 721000 110)
 (.entry 721006 111))))
 (.branch 721761
 (.branch 721751
 (.entry 721738 112)
 (.branch 721760
 (.entry 721751 113)
 (.entry 721760 114)))
 (.branch 721762
 (.entry 721761 115)
 (.branch 721763
 (.entry 721762 116)
 (.entry 721763 117))))))
 (.branch 721838
 (.branch 721811
 (.branch 721786
 (.branch 721784
 (.entry 721775 118)
 (.branch 721785
 (.entry 721784 119)
 (.entry 721785 120)))
 (.branch 721787
 (.entry 721786 121)
 (.branch 721798
 (.entry 721787 122)
 (.entry 721798 123))))
 (.branch 721828
 (.branch 721822
 (.entry 721811 124)
 (.branch 721826
 (.entry 721822 125)
 (.entry 721826 126)))
 (.branch 721834
 (.entry 721828 127)
 (.branch 721835
 (.entry 721834 128)
 (.entry 721835 129)))))
 (.branch 721852
 (.branch 721847
 (.branch 721840
 (.entry 721838 130)
 (.branch 721846
 (.entry 721840 131)
 (.entry 721846 132)))
 (.branch 721848
 (.entry 721847 133)
 (.branch 721850
 (.entry 721848 134)
 (.entry 721850 135))))
 (.branch 721856
 (.branch 721853
 (.entry 721852 136)
 (.branch 721855
 (.entry 721853 137)
 (.entry 721855 138)))
 (.branch 721857
 (.entry 721856 139)
 (.branch 721859
 (.entry 721857 140)
 (.entry 721859 141)))))))
 (.branch 725519
 (.branch 724442
 (.branch 721869
 (.branch 721864
 (.branch 721862
 (.entry 721861 142)
 (.branch 721863
 (.entry 721862 143)
 (.entry 721863 144)))
 (.branch 721866
 (.entry 721864 145)
 (.branch 721868
 (.entry 721866 146)
 (.entry 721868 147))))
 (.branch 724355
 (.branch 721870
 (.entry 721869 148)
 (.branch 724354
 (.entry 721870 149)
 (.entry 724354 150)))
 (.branch 724378
 (.entry 724355 151)
 (.branch 724379
 (.entry 724378 152)
 (.entry 724379 153)))))
 (.branch 725482
 (.branch 724454
 (.branch 724444
 (.entry 724442 154)
 (.branch 724451
 (.entry 724444 155)
 (.entry 724451 156)))
 (.branch 724456
 (.entry 724454 157)
 (.branch 724462
 (.entry 724456 158)
 (.entry 724462 159))))
 (.branch 725505
 (.branch 725495
 (.entry 725482 160)
 (.branch 725504
 (.entry 725495 161)
 (.entry 725504 162)))
 (.branch 725506
 (.entry 725505 163)
 (.branch 725507
 (.entry 725506 164)
 (.entry 725507 165))))))
 (.branch 725582
 (.branch 725555
 (.branch 725530
 (.branch 725528
 (.entry 725519 166)
 (.branch 725529
 (.entry 725528 167)
 (.entry 725529 168)))
 (.branch 725531
 (.entry 725530 169)
 (.branch 725542
 (.entry 725531 170)
 (.entry 725542 171))))
 (.branch 725572
 (.branch 725566
 (.entry 725555 172)
 (.branch 725570
 (.entry 725566 173)
 (.entry 725570 174)))
 (.branch 725578
 (.entry 725572 175)
 (.branch 725579
 (.entry 725578 176)
 (.entry 725579 177)))))
 (.branch 725596
 (.branch 725591
 (.branch 725584
 (.entry 725582 178)
 (.branch 725590
 (.entry 725584 179)
 (.entry 725590 180)))
 (.branch 725592
 (.entry 725591 181)
 (.branch 725594
 (.entry 725592 182)
 (.entry 725594 183))))
 (.branch 725600
 (.branch 725597
 (.entry 725596 184)
 (.branch 725599
 (.entry 725597 185)
 (.entry 725599 186)))
 (.branch 725601
 (.entry 725600 187)
 (.branch 725603
 (.entry 725601 188)
 (.entry 725603 189)))))))))
 (.branch 803188
 (.branch 792827
 (.branch 744326
 (.branch 727342
 (.branch 725612
 (.branch 725607
 (.branch 725606
 (.entry 725605 190)
 (.entry 725606 191))
 (.branch 725608
 (.entry 725607 192)
 (.branch 725610
 (.entry 725608 193)
 (.entry 725610 194))))
 (.branch 727043
 (.branch 725613
 (.entry 725612 195)
 (.branch 725614
 (.entry 725613 196)
 (.entry 725614 197)))
 (.branch 727054
 (.entry 727043 198)
 (.branch 727331
 (.entry 727054 199)
 (.entry 727331 200)))))
 (.branch 744227
 (.branch 729059
 (.branch 728771
 (.entry 727342 201)
 (.branch 728782
 (.entry 728771 202)
 (.entry 728782 203)))
 (.branch 729070
 (.entry 729059 204)
 (.branch 744226
 (.entry 729070 205)
 (.entry 744226 206))))
 (.branch 744314
 (.branch 744250
 (.entry 744227 207)
 (.branch 744251
 (.entry 744250 208)
 (.entry 744251 209)))
 (.branch 744316
 (.entry 744314 210)
 (.branch 744323
 (.entry 744316 211)
 (.entry 744323 212))))))
 (.branch 746350
 (.branch 746267
 (.branch 746242
 (.branch 744328
 (.entry 744326 213)
 (.branch 744334
 (.entry 744328 214)
 (.entry 744334 215)))
 (.branch 746243
 (.entry 746242 216)
 (.branch 746266
 (.entry 746243 217)
 (.entry 746266 218))))
 (.branch 746339
 (.branch 746330
 (.entry 746267 219)
 (.branch 746332
 (.entry 746330 220)
 (.entry 746332 221)))
 (.branch 746342
 (.entry 746339 222)
 (.branch 746344
 (.entry 746342 223)
 (.entry 746344 224)))))
 (.branch 792142
 (.branch 787667
 (.branch 785795
 (.entry 746350 225)
 (.branch 785806
 (.entry 785795 226)
 (.entry 785806 227)))
 (.branch 787678
 (.entry 787667 228)
 (.branch 792131
 (.entry 787678 229)
 (.entry 792131 230))))
 (.branch 792563
 (.branch 792419
 (.entry 792142 231)
 (.branch 792430
 (.entry 792419 232)
 (.entry 792430 233)))
 (.branch 792574
 (.entry 792563 234)
 (.branch 792826
 (.entry 792574 235)
 (.entry 792826 236)))))))
 (.branch 802403
 (.branch 793127
 (.branch 792860
 (.branch 792848
 (.branch 792838
 (.entry 792827 237)
 (.branch 792839
 (.entry 792838 238)
 (.entry 792839 239)))
 (.branch 792849
 (.entry 792848 240)
 (.branch 792851
 (.entry 792849 241)
 (.entry 792851 242))))
 (.branch 793114
 (.branch 792861
 (.entry 792860 243)
 (.branch 792862
 (.entry 792861 244)
 (.entry 792862 245)))
 (.branch 793115
 (.entry 793114 246)
 (.branch 793126
 (.entry 793115 247)
 (.entry 793126 248)))))
 (.branch 793150
 (.branch 793139
 (.branch 793136
 (.entry 793127 249)
 (.branch 793137
 (.entry 793136 250)
 (.entry 793137 251)))
 (.branch 793148
 (.entry 793139 252)
 (.branch 793149
 (.entry 793148 253)
 (.entry 793149 254))))
 (.branch 800771
 (.branch 799043
 (.entry 793150 255)
 (.branch 799054
 (.entry 799043 256)
 (.entry 799054 257)))
 (.branch 800782
 (.entry 800771 258)
 (.branch 802402
 (.entry 800782 259)
 (.entry 802402 260))))))
 (.branch 803121
 (.branch 802502
 (.branch 802490
 (.branch 802426
 (.entry 802403 261)
 (.branch 802427
 (.entry 802426 262)
 (.entry 802427 263)))
 (.branch 802492
 (.entry 802490 264)
 (.branch 802499
 (.entry 802492 265)
 (.entry 802499 266))))
 (.branch 803098
 (.branch 802504
 (.entry 802502 267)
 (.branch 802510
 (.entry 802504 268)
 (.entry 802510 269)))
 (.branch 803111
 (.entry 803098 270)
 (.branch 803120
 (.entry 803111 271)
 (.entry 803120 272)))))
 (.branch 803146
 (.branch 803135
 (.branch 803122
 (.entry 803121 273)
 (.branch 803123
 (.entry 803122 274)
 (.entry 803123 275)))
 (.branch 803144
 (.entry 803135 276)
 (.branch 803145
 (.entry 803144 277)
 (.entry 803145 278))))
 (.branch 803171
 (.branch 803147
 (.entry 803146 279)
 (.branch 803158
 (.entry 803147 280)
 (.entry 803158 281)))
 (.branch 803182
 (.entry 803171 282)
 (.branch 803186
 (.entry 803182 283)
 (.entry 803186 284))))))))
 (.branch 806930
 (.branch 805858
 (.branch 803215
 (.branch 803206
 (.branch 803195
 (.branch 803194
 (.entry 803188 285)
 (.entry 803194 286))
 (.branch 803198
 (.entry 803195 287)
 (.branch 803200
 (.entry 803198 288)
 (.entry 803200 289))))
 (.branch 803210
 (.branch 803207
 (.entry 803206 290)
 (.branch 803208
 (.entry 803207 291)
 (.entry 803208 292)))
 (.branch 803212
 (.entry 803210 293)
 (.branch 803213
 (.entry 803212 294)
 (.entry 803213 295)))))
 (.branch 803223
 (.branch 803219
 (.branch 803216
 (.entry 803215 296)
 (.branch 803217
 (.entry 803216 297)
 (.entry 803217 298)))
 (.branch 803221
 (.entry 803219 299)
 (.branch 803222
 (.entry 803221 300)
 (.entry 803222 301))))
 (.branch 803228
 (.branch 803224
 (.entry 803223 302)
 (.branch 803226
 (.entry 803224 303)
 (.entry 803226 304)))
 (.branch 803229
 (.entry 803228 305)
 (.branch 803230
 (.entry 803229 306)
 (.entry 803230 307))))))
 (.branch 806864
 (.branch 805955
 (.branch 805883
 (.branch 805859
 (.entry 805858 308)
 (.branch 805882
 (.entry 805859 309)
 (.entry 805882 310)))
 (.branch 805946
 (.entry 805883 311)
 (.branch 805948
 (.entry 805946 312)
 (.entry 805948 313))))
 (.branch 805966
 (.branch 805958
 (.entry 805955 314)
 (.branch 805960
 (.entry 805958 315)
 (.entry 805960 316)))
 (.branch 806842
 (.entry 805966 317)
 (.branch 806855
 (.entry 806842 318)
 (.entry 806855 319)))))
 (.branch 806889
 (.branch 806867
 (.branch 806865
 (.entry 806864 320)
 (.branch 806866
 (.entry 806865 321)
 (.entry 806866 322)))
 (.branch 806879
 (.entry 806867 323)
 (.branch 806888
 (.entry 806879 324)
 (.entry 806888 325))))
 (.branch 806902
 (.branch 806890
 (.entry 806889 326)
 (.branch 806891
 (.entry 806890 327)
 (.entry 806891 328)))
 (.branch 806915
 (.entry 806902 329)
 (.branch 806926
 (.entry 806915 330)
 (.entry 806926 331)))))))
 (.branch 810131
 (.branch 806959
 (.branch 806950
 (.branch 806939
 (.branch 806932
 (.entry 806930 332)
 (.branch 806938
 (.entry 806932 333)
 (.entry 806938 334)))
 (.branch 806942
 (.entry 806939 335)
 (.branch 806944
 (.entry 806942 336)
 (.entry 806944 337))))
 (.branch 806954
 (.branch 806951
 (.entry 806950 338)
 (.branch 806952
 (.entry 806951 339)
 (.entry 806952 340)))
 (.branch 806956
 (.entry 806954 341)
 (.branch 806957
 (.entry 806956 342)
 (.entry 806957 343)))))
 (.branch 806967
 (.branch 806963
 (.branch 806960
 (.entry 806959 344)
 (.branch 806961
 (.entry 806960 345)
 (.entry 806961 346)))
 (.branch 806965
 (.entry 806963 347)
 (.branch 806966
 (.entry 806965 348)
 (.entry 806966 349))))
 (.branch 806972
 (.branch 806968
 (.entry 806967 350)
 (.branch 806970
 (.entry 806968 351)
 (.entry 806970 352)))
 (.branch 806973
 (.entry 806972 353)
 (.branch 806974
 (.entry 806973 354)
 (.entry 806974 355))))))
 (.branch 827690
 (.branch 812147
 (.branch 810430
 (.branch 810142
 (.entry 810131 356)
 (.branch 810419
 (.entry 810142 357)
 (.entry 810419 358)))
 (.branch 811859
 (.entry 810430 359)
 (.branch 811870
 (.entry 811859 360)
 (.entry 811870 361))))
 (.branch 827603
 (.branch 812158
 (.entry 812147 362)
 (.branch 827602
 (.entry 812158 363)
 (.entry 827602 364)))
 (.branch 827626
 (.entry 827603 365)
 (.branch 827627
 (.entry 827626 366)
 (.entry 827627 367)))))
 (.branch 829042
 (.branch 827702
 (.branch 827692
 (.entry 827690 368)
 (.branch 827699
 (.entry 827692 369)
 (.entry 827699 370)))
 (.branch 827704
 (.entry 827702 371)
 (.branch 827710
 (.entry 827704 372)
 (.entry 827710 373))))
 (.branch 829067
 (.branch 829043
 (.entry 829042 374)
 (.branch 829066
 (.entry 829043 375)
 (.entry 829066 376)))
 (.branch 829130
 (.entry 829067 377)
 (.branch 829132
 (.entry 829130 378)
 (.entry 829132 379))))))))))
 (.branch 1057237
 (.branch 1045436
 (.branch 947806
 (.branch 929207
 (.branch 887758
 (.branch 868750
 (.branch 829144
 (.branch 829142
 (.entry 829139 380)
 (.entry 829142 381))
 (.branch 829150
 (.entry 829144 382)
 (.branch 868739
 (.entry 829150 383)
 (.entry 868739 384))))
 (.branch 886163
 (.branch 870611
 (.entry 868750 385)
 (.branch 870622
 (.entry 870611 386)
 (.entry 870622 387)))
 (.branch 886174
 (.entry 886163 388)
 (.branch 887747
 (.entry 886174 389)
 (.entry 887747 390)))))
 (.branch 928510
 (.branch 908483
 (.branch 906899
 (.entry 887758 391)
 (.branch 906910
 (.entry 906899 392)
 (.entry 906910 393)))
 (.branch 908494
 (.entry 908483 394)
 (.branch 928499
 (.entry 908494 395)
 (.entry 928499 396))))
 (.branch 929194
 (.branch 928787
 (.entry 928510 397)
 (.branch 928798
 (.entry 928787 398)
 (.entry 928798 399)))
 (.branch 929195
 (.entry 929194 400)
 (.branch 929206
 (.entry 929195 401)
 (.entry 929206 402))))))
 (.branch 932795
 (.branch 929230
 (.branch 929219
 (.branch 929216
 (.entry 929207 403)
 (.branch 929217
 (.entry 929216 404)
 (.entry 929217 405)))
 (.branch 929228
 (.entry 929219 406)
 (.branch 929229
 (.entry 929228 407)
 (.entry 929229 408))))
 (.branch 932243
 (.branch 931955
 (.entry 929230 409)
 (.branch 931966
 (.entry 931955 410)
 (.entry 931966 411)))
 (.branch 932254
 (.entry 932243 412)
 (.branch 932794
 (.entry 932254 413)
 (.entry 932794 414)))))
 (.branch 932828
 (.branch 932816
 (.branch 932806
 (.entry 932795 415)
 (.branch 932807
 (.entry 932806 416)
 (.entry 932807 417)))
 (.branch 932817
 (.entry 932816 418)
 (.branch 932819
 (.entry 932817 419)
 (.entry 932819 420))))
 (.branch 947507
 (.branch 932829
 (.entry 932828 421)
 (.branch 932830
 (.entry 932829 422)
 (.entry 932830 423)))
 (.branch 947518
 (.entry 947507 424)
 (.branch 947795
 (.entry 947518 425)
 (.entry 947795 426)))))))
 (.branch 951694
 (.branch 950974
 (.branch 948369
 (.branch 948358
 (.branch 948346
 (.entry 947806 427)
 (.branch 948347
 (.entry 948346 428)
 (.entry 948347 429)))
 (.branch 948359
 (.entry 948358 430)
 (.branch 948368
 (.entry 948359 431)
 (.entry 948368 432))))
 (.branch 948381
 (.branch 948371
 (.entry 948369 433)
 (.branch 948380
 (.entry 948371 434)
 (.entry 948380 435)))
 (.branch 948382
 (.entry 948381 436)
 (.branch 950963
 (.entry 948382 437)
 (.entry 950963 438)))))
 (.branch 951671
 (.branch 951658
 (.branch 951251
 (.entry 950974 439)
 (.branch 951262
 (.entry 951251 440)
 (.entry 951262 441)))
 (.branch 951659
 (.entry 951658 442)
 (.branch 951670
 (.entry 951659 443)
 (.entry 951670 444))))
 (.branch 951683
 (.branch 951680
 (.entry 951671 445)
 (.branch 951681
 (.entry 951680 446)
 (.entry 951681 447)))
 (.branch 951692
 (.entry 951683 448)
 (.branch 951693
 (.entry 951692 449)
 (.entry 951693 450))))))
 (.branch 1045137
 (.branch 1044862
 (.branch 1044707
 (.branch 1044419
 (.entry 951694 451)
 (.branch 1044430
 (.entry 1044419 452)
 (.entry 1044430 453)))
 (.branch 1044718
 (.entry 1044707 454)
 (.branch 1044851
 (.entry 1044718 455)
 (.entry 1044851 456))))
 (.branch 1045126
 (.branch 1045114
 (.entry 1044862 457)
 (.branch 1045115
 (.entry 1045114 458)
 (.entry 1045115 459)))
 (.branch 1045127
 (.entry 1045126 460)
 (.branch 1045136
 (.entry 1045127 461)
 (.entry 1045136 462)))))
 (.branch 1045403
 (.branch 1045149
 (.branch 1045139
 (.entry 1045137 463)
 (.branch 1045148
 (.entry 1045139 464)
 (.entry 1045148 465)))
 (.branch 1045150
 (.entry 1045149 466)
 (.branch 1045402
 (.entry 1045150 467)
 (.entry 1045402 468))))
 (.branch 1045424
 (.branch 1045414
 (.entry 1045403 469)
 (.branch 1045415
 (.entry 1045414 470)
 (.entry 1045415 471)))
 (.branch 1045425
 (.entry 1045424 472)
 (.branch 1045427
 (.entry 1045425 473)
 (.entry 1045427 474))))))))
 (.branch 1054069
 (.branch 1053983
 (.branch 1053050
 (.branch 1049603
 (.branch 1045438
 (.branch 1045437
 (.entry 1045436 475)
 (.entry 1045437 476))
 (.branch 1047875
 (.entry 1045438 477)
 (.branch 1047886
 (.entry 1047875 478)
 (.entry 1047886 479))))
 (.branch 1052963
 (.branch 1049614
 (.entry 1049603 480)
 (.branch 1052962
 (.entry 1049614 481)
 (.entry 1052962 482)))
 (.branch 1052986
 (.entry 1052963 483)
 (.branch 1052987
 (.entry 1052986 484)
 (.entry 1052987 485)))))
 (.branch 1053946
 (.branch 1053062
 (.branch 1053052
 (.entry 1053050 486)
 (.branch 1053059
 (.entry 1053052 487)
 (.entry 1053059 488)))
 (.branch 1053064
 (.entry 1053062 489)
 (.branch 1053070
 (.entry 1053064 490)
 (.entry 1053070 491))))
 (.branch 1053969
 (.branch 1053959
 (.entry 1053946 492)
 (.branch 1053968
 (.entry 1053959 493)
 (.entry 1053968 494)))
 (.branch 1053970
 (.entry 1053969 495)
 (.branch 1053971
 (.entry 1053970 496)
 (.entry 1053971 497))))))
 (.branch 1054046
 (.branch 1054019
 (.branch 1053994
 (.branch 1053992
 (.entry 1053983 498)
 (.branch 1053993
 (.entry 1053992 499)
 (.entry 1053993 500)))
 (.branch 1053995
 (.entry 1053994 501)
 (.branch 1054006
 (.entry 1053995 502)
 (.entry 1054006 503))))
 (.branch 1054036
 (.branch 1054030
 (.entry 1054019 504)
 (.branch 1054034
 (.entry 1054030 505)
 (.entry 1054034 506)))
 (.branch 1054042
 (.entry 1054036 507)
 (.branch 1054043
 (.entry 1054042 508)
 (.entry 1054043 509)))))
 (.branch 1054060
 (.branch 1054055
 (.branch 1054048
 (.entry 1054046 510)
 (.branch 1054054
 (.entry 1054048 511)
 (.entry 1054054 512)))
 (.branch 1054056
 (.entry 1054055 513)
 (.branch 1054058
 (.entry 1054056 514)
 (.entry 1054058 515))))
 (.branch 1054064
 (.branch 1054061
 (.entry 1054060 516)
 (.branch 1054063
 (.entry 1054061 517)
 (.entry 1054063 518)))
 (.branch 1054065
 (.entry 1054064 519)
 (.branch 1054067
 (.entry 1054065 520)
 (.entry 1054067 521)))))))
 (.branch 1057151
 (.branch 1056506
 (.branch 1054077
 (.branch 1054072
 (.branch 1054070
 (.entry 1054069 522)
 (.branch 1054071
 (.entry 1054070 523)
 (.entry 1054071 524)))
 (.branch 1054074
 (.entry 1054072 525)
 (.branch 1054076
 (.entry 1054074 526)
 (.entry 1054076 527))))
 (.branch 1056419
 (.branch 1054078
 (.entry 1054077 528)
 (.branch 1056418
 (.entry 1054078 529)
 (.entry 1056418 530)))
 (.branch 1056442
 (.entry 1056419 531)
 (.branch 1056443
 (.entry 1056442 532)
 (.entry 1056443 533)))))
 (.branch 1057114
 (.branch 1056518
 (.branch 1056508
 (.entry 1056506 534)
 (.branch 1056515
 (.entry 1056508 535)
 (.entry 1056515 536)))
 (.branch 1056520
 (.entry 1056518 537)
 (.branch 1056526
 (.entry 1056520 538)
 (.entry 1056526 539))))
 (.branch 1057137
 (.branch 1057127
 (.entry 1057114 540)
 (.branch 1057136
 (.entry 1057127 541)
 (.entry 1057136 542)))
 (.branch 1057138
 (.entry 1057137 543)
 (.branch 1057139
 (.entry 1057138 544)
 (.entry 1057139 545))))))
 (.branch 1057214
 (.branch 1057187
 (.branch 1057162
 (.branch 1057160
 (.entry 1057151 546)
 (.branch 1057161
 (.entry 1057160 547)
 (.entry 1057161 548)))
 (.branch 1057163
 (.entry 1057162 549)
 (.branch 1057174
 (.entry 1057163 550)
 (.entry 1057174 551))))
 (.branch 1057204
 (.branch 1057198
 (.entry 1057187 552)
 (.branch 1057202
 (.entry 1057198 553)
 (.entry 1057202 554)))
 (.branch 1057210
 (.entry 1057204 555)
 (.branch 1057211
 (.entry 1057210 556)
 (.entry 1057211 557)))))
 (.branch 1057228
 (.branch 1057223
 (.branch 1057216
 (.entry 1057214 558)
 (.branch 1057222
 (.entry 1057216 559)
 (.entry 1057222 560)))
 (.branch 1057224
 (.entry 1057223 561)
 (.branch 1057226
 (.entry 1057224 562)
 (.entry 1057226 563))))
 (.branch 1057232
 (.branch 1057229
 (.entry 1057228 564)
 (.branch 1057231
 (.entry 1057229 565)
 (.entry 1057231 566)))
 (.branch 1057233
 (.entry 1057232 567)
 (.branch 1057235
 (.entry 1057233 568)
 (.entry 1057235 569)))))))))
 (.branch 1095982
 (.branch 1092526
 (.branch 1083022
 (.branch 1082734
 (.branch 1057244
 (.branch 1057239
 (.branch 1057238
 (.entry 1057237 570)
 (.entry 1057238 571))
 (.branch 1057240
 (.entry 1057239 572)
 (.branch 1057242
 (.entry 1057240 573)
 (.entry 1057242 574))))
 (.branch 1082147
 (.branch 1057245
 (.entry 1057244 575)
 (.branch 1057246
 (.entry 1057245 576)
 (.entry 1057246 577)))
 (.branch 1082158
 (.entry 1082147 578)
 (.branch 1082723
 (.entry 1082158 579)
 (.entry 1082723 580)))))
 (.branch 1082999
 (.branch 1082986
 (.branch 1082867
 (.entry 1082734 581)
 (.branch 1082878
 (.entry 1082867 582)
 (.entry 1082878 583)))
 (.branch 1082987
 (.entry 1082986 584)
 (.branch 1082998
 (.entry 1082987 585)
 (.entry 1082998 586))))
 (.branch 1083011
 (.branch 1083008
 (.entry 1082999 587)
 (.branch 1083009
 (.entry 1083008 588)
 (.entry 1083009 589)))
 (.branch 1083020
 (.entry 1083011 590)
 (.branch 1083021
 (.entry 1083020 591)
 (.entry 1083021 592))))))
 (.branch 1089070
 (.branch 1083297
 (.branch 1083286
 (.branch 1083274
 (.entry 1083022 593)
 (.branch 1083275
 (.entry 1083274 594)
 (.entry 1083275 595)))
 (.branch 1083287
 (.entry 1083286 596)
 (.branch 1083296
 (.entry 1083287 597)
 (.entry 1083296 598))))
 (.branch 1083309
 (.branch 1083299
 (.entry 1083297 599)
 (.branch 1083308
 (.entry 1083299 600)
 (.entry 1083308 601)))
 (.branch 1083310
 (.entry 1083309 602)
 (.branch 1089059
 (.entry 1083310 603)
 (.entry 1089059 604)))))
 (.branch 1092443
 (.branch 1092418
 (.branch 1090787
 (.entry 1089070 605)
 (.branch 1090798
 (.entry 1090787 606)
 (.entry 1090798 607)))
 (.branch 1092419
 (.entry 1092418 608)
 (.branch 1092442
 (.entry 1092419 609)
 (.entry 1092442 610))))
 (.branch 1092515
 (.branch 1092506
 (.entry 1092443 611)
 (.branch 1092508
 (.entry 1092506 612)
 (.entry 1092508 613)))
 (.branch 1092518
 (.entry 1092515 614)
 (.branch 1092520
 (.entry 1092518 615)
 (.entry 1092520 616)))))))
 (.branch 1093658
 (.branch 1093606
 (.branch 1093571
 (.branch 1093568
 (.branch 1093546
 (.entry 1092526 617)
 (.branch 1093559
 (.entry 1093546 618)
 (.entry 1093559 619)))
 (.branch 1093569
 (.entry 1093568 620)
 (.branch 1093570
 (.entry 1093569 621)
 (.entry 1093570 622))))
 (.branch 1093593
 (.branch 1093583
 (.entry 1093571 623)
 (.branch 1093592
 (.entry 1093583 624)
 (.entry 1093592 625)))
 (.branch 1093594
 (.entry 1093593 626)
 (.branch 1093595
 (.entry 1093594 627)
 (.entry 1093595 628)))))
 (.branch 1093643
 (.branch 1093634
 (.branch 1093619
 (.entry 1093606 629)
 (.branch 1093630
 (.entry 1093619 630)
 (.entry 1093630 631)))
 (.branch 1093636
 (.entry 1093634 632)
 (.branch 1093642
 (.entry 1093636 633)
 (.entry 1093642 634))))
 (.branch 1093654
 (.branch 1093646
 (.entry 1093643 635)
 (.branch 1093648
 (.entry 1093646 636)
 (.entry 1093648 637)))
 (.branch 1093655
 (.entry 1093654 638)
 (.branch 1093656
 (.entry 1093655 639)
 (.entry 1093656 640))))))
 (.branch 1093676
 (.branch 1093667
 (.branch 1093663
 (.branch 1093660
 (.entry 1093658 641)
 (.branch 1093661
 (.entry 1093660 642)
 (.entry 1093661 643)))
 (.branch 1093664
 (.entry 1093663 644)
 (.branch 1093665
 (.entry 1093664 645)
 (.entry 1093665 646))))
 (.branch 1093671
 (.branch 1093669
 (.entry 1093667 647)
 (.branch 1093670
 (.entry 1093669 648)
 (.entry 1093670 649)))
 (.branch 1093672
 (.entry 1093671 650)
 (.branch 1093674
 (.entry 1093672 651)
 (.entry 1093674 652)))))
 (.branch 1095899
 (.branch 1095874
 (.branch 1093677
 (.entry 1093676 653)
 (.branch 1093678
 (.entry 1093677 654)
 (.entry 1093678 655)))
 (.branch 1095875
 (.entry 1095874 656)
 (.branch 1095898
 (.entry 1095875 657)
 (.entry 1095898 658))))
 (.branch 1095971
 (.branch 1095962
 (.entry 1095899 659)
 (.branch 1095964
 (.entry 1095962 660)
 (.entry 1095964 661)))
 (.branch 1095974
 (.entry 1095971 662)
 (.branch 1095976
 (.entry 1095974 663)
 (.entry 1095976 664))))))))
 (.branch 1176514
 (.branch 1096824
 (.branch 1096763
 (.branch 1096738
 (.branch 1096727
 (.branch 1096714
 (.entry 1095982 665)
 (.entry 1096714 666))
 (.branch 1096736
 (.entry 1096727 667)
 (.branch 1096737
 (.entry 1096736 668)
 (.entry 1096737 669))))
 (.branch 1096760
 (.branch 1096739
 (.entry 1096738 670)
 (.branch 1096751
 (.entry 1096739 671)
 (.entry 1096751 672)))
 (.branch 1096761
 (.entry 1096760 673)
 (.branch 1096762
 (.entry 1096761 674)
 (.entry 1096762 675)))))
 (.branch 1096810
 (.branch 1096798
 (.branch 1096774
 (.entry 1096763 676)
 (.branch 1096787
 (.entry 1096774 677)
 (.entry 1096787 678)))
 (.branch 1096802
 (.entry 1096798 679)
 (.branch 1096804
 (.entry 1096802 680)
 (.entry 1096804 681))))
 (.branch 1096816
 (.branch 1096811
 (.entry 1096810 682)
 (.branch 1096814
 (.entry 1096811 683)
 (.entry 1096814 684)))
 (.branch 1096822
 (.entry 1096816 685)
 (.branch 1096823
 (.entry 1096822 686)
 (.entry 1096823 687))))))
 (.branch 1096842
 (.branch 1096833
 (.branch 1096829
 (.branch 1096826
 (.entry 1096824 688)
 (.branch 1096828
 (.entry 1096826 689)
 (.entry 1096828 690)))
 (.branch 1096831
 (.entry 1096829 691)
 (.branch 1096832
 (.entry 1096831 692)
 (.entry 1096832 693))))
 (.branch 1096838
 (.branch 1096835
 (.entry 1096833 694)
 (.branch 1096837
 (.entry 1096835 695)
 (.entry 1096837 696)))
 (.branch 1096839
 (.entry 1096838 697)
 (.branch 1096840
 (.entry 1096839 698)
 (.entry 1096840 699)))))
 (.branch 1167971
 (.branch 1096846
 (.branch 1096844
 (.entry 1096842 700)
 (.branch 1096845
 (.entry 1096844 701)
 (.entry 1096845 702)))
 (.branch 1167683
 (.entry 1096846 703)
 (.branch 1167694
 (.entry 1167683 704)
 (.entry 1167694 705))))
 (.branch 1171150
 (.branch 1167982
 (.entry 1167971 706)
 (.branch 1171139
 (.entry 1167982 707)
 (.entry 1171139 708)))
 (.branch 1171427
 (.entry 1171150 709)
 (.branch 1171438
 (.entry 1171427 710)
 (.entry 1171438 711)))))))
 (.branch 1212755
 (.branch 1177978
 (.branch 1176611
 (.branch 1176539
 (.branch 1176515
 (.entry 1176514 712)
 (.branch 1176538
 (.entry 1176515 713)
 (.entry 1176538 714)))
 (.branch 1176602
 (.entry 1176539 715)
 (.branch 1176604
 (.entry 1176602 716)
 (.entry 1176604 717))))
 (.branch 1176622
 (.branch 1176614
 (.entry 1176611 718)
 (.branch 1176616
 (.entry 1176614 719)
 (.entry 1176616 720)))
 (.branch 1177954
 (.entry 1176622 721)
 (.branch 1177955
 (.entry 1177954 722)
 (.entry 1177955 723)))))
 (.branch 1178056
 (.branch 1178044
 (.branch 1177979
 (.entry 1177978 724)
 (.branch 1178042
 (.entry 1177979 725)
 (.entry 1178042 726)))
 (.branch 1178051
 (.entry 1178044 727)
 (.branch 1178054
 (.entry 1178051 728)
 (.entry 1178054 729))))
 (.branch 1209310
 (.branch 1178062
 (.entry 1178056 730)
 (.branch 1209299
 (.entry 1178062 731)
 (.entry 1209299 732)))
 (.branch 1209587
 (.entry 1209310 733)
 (.branch 1209598
 (.entry 1209587 734)
 (.entry 1209598 735))))))
 (.branch 1217944
 (.branch 1217866
 (.branch 1213054
 (.branch 1212766
 (.entry 1212755 736)
 (.branch 1213043
 (.entry 1212766 737)
 (.entry 1213043 738)))
 (.branch 1217842
 (.entry 1213054 739)
 (.branch 1217843
 (.entry 1217842 740)
 (.entry 1217843 741))))
 (.branch 1217932
 (.branch 1217867
 (.entry 1217866 742)
 (.branch 1217930
 (.entry 1217867 743)
 (.entry 1217930 744)))
 (.branch 1217939
 (.entry 1217932 745)
 (.branch 1217942
 (.entry 1217939 746)
 (.entry 1217942 747)))))
 (.branch 1219946
 (.branch 1219859
 (.branch 1217950
 (.entry 1217944 748)
 (.branch 1219858
 (.entry 1217950 749)
 (.entry 1219858 750)))
 (.branch 1219882
 (.entry 1219859 751)
 (.branch 1219883
 (.entry 1219882 752)
 (.entry 1219883 753))))
 (.branch 1219958
 (.branch 1219948
 (.entry 1219946 754)
 (.branch 1219955
 (.entry 1219948 755)
 (.entry 1219955 756)))
 (.branch 1219960
 (.entry 1219958 757)
 (.branch 1219966
 (.entry 1219960 758)
 (.entry 1219966 759)))))))))))
lemma table_correct : table.Correct caseKey := by decide +kernel

lemma exists_case {j : ℕ} (h : (table.lookup j).isSome = true) :
    ∃ i : Cases, table.lookup j = some i ∧ caseKey i = j :=
  table.exists_of_isSome caseKey table_correct j h

#print axioms table_correct
#print axioms exists_case
end Erdos184Work.PureFiveFilter4
