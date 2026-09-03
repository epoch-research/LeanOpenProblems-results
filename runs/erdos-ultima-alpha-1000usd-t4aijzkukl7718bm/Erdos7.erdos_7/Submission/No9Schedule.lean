import Submission.No9CheckedTransitions

/-! Ordered offsets and a decomposition of the finite small-prime schedule. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def blockOffset (i : ℕ) : ℕ := (if i < 144 then (if i < 72 then (if i < 36 then (if i < 18 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 668 else 680) else (if i < 3 then 691 else 702)) else (if i < 6 then (if i < 5 then 713 else 729) else (if i < 7 then 738 else (if i < 8 then 755 else 770)))) else (if i < 13 then (if i < 11 then (if i < 10 then 780 else 794) else (if i < 12 then 809 else 825)) else (if i < 15 then (if i < 14 then 839 else 852) else (if i < 16 then 867 else (if i < 17 then 884 else 900))))) else (if i < 27 then (if i < 22 then (if i < 20 then (if i < 19 then 913 else 928) else (if i < 21 then 941 else 963)) else (if i < 24 then (if i < 23 then 981 else 996) else (if i < 25 then 1011 else (if i < 26 then 1028 else 1048)))) else (if i < 31 then (if i < 29 then (if i < 28 then 1065 else 1086) else (if i < 30 then 1107 else 1126)) else (if i < 33 then (if i < 32 then 1145 else 1169) else (if i < 34 then 1188 else (if i < 35 then 1210 else 1230)))))) else (if i < 54 then (if i < 45 then (if i < 40 then (if i < 38 then (if i < 37 then 1252 else 1273) else (if i < 39 then 1296 else 1317)) else (if i < 42 then (if i < 41 then 1339 else 1364) else (if i < 43 then 1387 else (if i < 44 then 1408 else 1435)))) else (if i < 49 then (if i < 47 then (if i < 46 then 1459 else 1486) else (if i < 48 then 1517 else 1543)) else (if i < 51 then (if i < 50 then 1572 else 1598) else (if i < 52 then 1628 else (if i < 53 then 1655 else 1678))))) else (if i < 63 then (if i < 58 then (if i < 56 then (if i < 55 then 1709 else 1745) else (if i < 57 then 1774 else 1809)) else (if i < 60 then (if i < 59 then 1844 else 1876) else (if i < 61 then 1907 else (if i < 62 then 1937 else 1972)))) else (if i < 67 then (if i < 65 then (if i < 64 then 2006 else 2042) else (if i < 66 then 2081 else 2121)) else (if i < 69 then (if i < 68 then 2149 else 2185) else (if i < 70 then 2225 else (if i < 71 then 2268 else 2309))))))) else (if i < 108 then (if i < 90 then (if i < 81 then (if i < 76 then (if i < 74 then (if i < 73 then 2346 else 2390) else (if i < 75 then 2435 else 2484)) else (if i < 78 then (if i < 77 then 2523 else 2572) else (if i < 79 then 2613 else (if i < 80 then 2666 else 2713)))) else (if i < 85 then (if i < 83 then (if i < 82 then 2756 else 2806) else (if i < 84 then 2855 else 2907)) else (if i < 87 then (if i < 86 then 2962 else 3009) else (if i < 88 then 3066 else (if i < 89 then 3123 else 3178))))) else (if i < 99 then (if i < 94 then (if i < 92 then (if i < 91 then 3229 else 3285) else (if i < 93 then 3342 else 3404)) else (if i < 96 then (if i < 95 then 3460 else 3529) else (if i < 97 then 3596 else (if i < 98 then 3660 else 3728)))) else (if i < 103 then (if i < 101 then (if i < 100 then 3792 else 3857) else (if i < 102 then 3932 else 4000)) else (if i < 105 then (if i < 104 then 4064 else 4143) else (if i < 106 then 4217 else (if i < 107 then 4288 else 4368)))))) else (if i < 126 then (if i < 117 then (if i < 112 then (if i < 110 then (if i < 109 then 4454 else 4530) else (if i < 111 then 4611 else 4691)) else (if i < 114 then (if i < 113 then 4770 else 4853) else (if i < 115 then 4945 else (if i < 116 then 5031 else 5126)))) else (if i < 121 then (if i < 119 then (if i < 118 then 5215 else 5314) else (if i < 120 then 5406 else 5504)) else (if i < 123 then (if i < 122 then 5602 else 5704) else (if i < 124 then 5815 else (if i < 125 then 5922 else 6032))))) else (if i < 135 then (if i < 130 then (if i < 128 then (if i < 127 then 6132 else 6240) else (if i < 129 then 6345 else 6459)) else (if i < 132 then (if i < 131 then 6580 else 6696) else (if i < 133 then 6816 else (if i < 134 then 6930 else 7060)))) else (if i < 139 then (if i < 137 then (if i < 136 then 7194 else 7322) else (if i < 138 then 7456 else 7584)) else (if i < 141 then (if i < 140 then 7723 else 7865) else (if i < 142 then 8012 else (if i < 143 then 8156 else 8301)))))))) else (if i < 216 then (if i < 180 then (if i < 162 then (if i < 153 then (if i < 148 then (if i < 146 then (if i < 145 then 8446 else 8590) else (if i < 147 then 8758 else 8911)) else (if i < 150 then (if i < 149 then 9081 else 9253) else (if i < 151 then 9412 else (if i < 152 then 9583 else 9756)))) else (if i < 157 then (if i < 155 then (if i < 154 then 9923 else 10105) else (if i < 156 then 10285 else 10473)) else (if i < 159 then (if i < 158 then 10661 else 10850) else (if i < 160 then 11049 else (if i < 161 then 11245 else 11457))))) else (if i < 171 then (if i < 166 then (if i < 164 then (if i < 163 then 11666 else 11877) else (if i < 165 then 12095 else 12311)) else (if i < 168 then (if i < 167 then 12536 else 12767) else (if i < 169 then 12997 else (if i < 170 then 13238 else 13466)))) else (if i < 175 then (if i < 173 then (if i < 172 then 13708 else 13967) else (if i < 174 then 14227 else 14484)) else (if i < 177 then (if i < 176 then 14740 else 15005) else (if i < 178 then 15273 else (if i < 179 then 15543 else 15827)))))) else (if i < 198 then (if i < 189 then (if i < 184 then (if i < 182 then (if i < 181 then 16114 else 16412) else (if i < 183 then 16710 else 17016)) else (if i < 186 then (if i < 185 then 17329 else 17643) else (if i < 187 then 17966 else (if i < 188 then 18285 else 18622)))) else (if i < 193 then (if i < 191 then (if i < 190 then 18976 else 19306) else (if i < 192 then 19662 else 20019)) else (if i < 195 then (if i < 194 then 20388 else 20751) else (if i < 196 then 21122 else (if i < 197 then 21511 else 21912))))) else (if i < 207 then (if i < 202 then (if i < 200 then (if i < 199 then 22304 else 22713) else (if i < 201 then 23120 else 23552)) else (if i < 204 then (if i < 203 then 23984 else 24417) else (if i < 205 then 24869 else (if i < 206 then 25312 else 25762)))) else (if i < 211 then (if i < 209 then (if i < 208 then 26218 else 26710) else (if i < 210 then 27201 else 27719)) else (if i < 213 then (if i < 212 then 28231 else 28743) else (if i < 214 then 29268 else (if i < 215 then 29802 else 30360))))))) else (if i < 252 then (if i < 234 then (if i < 225 then (if i < 220 then (if i < 218 then (if i < 217 then 30896 else 31466) else (if i < 219 then 32026 else 32608)) else (if i < 222 then (if i < 221 then 33208 else 33827) else (if i < 223 then 34416 else (if i < 224 then 35059 else 35703)))) else (if i < 229 then (if i < 227 then (if i < 226 then 36365 else 37035) else (if i < 228 then 37706 else 38390)) else (if i < 231 then (if i < 230 then 39085 else 39815) else (if i < 232 then 40536 else (if i < 233 then 41291 else 42050))))) else (if i < 243 then (if i < 238 then (if i < 236 then (if i < 235 then 42815 else 43623) else (if i < 237 then 44411 else 45210)) else (if i < 240 then (if i < 239 then 46032 else 46882) else (if i < 241 then 47749 else (if i < 242 then 48633 else 49530)))) else (if i < 247 then (if i < 245 then (if i < 244 then 50456 else 51348) else (if i < 246 then 52267 else 53245)) else (if i < 249 then (if i < 248 then 54211 else 55222) else (if i < 250 then 56238 else (if i < 251 then 57271 else 58326)))))) else (if i < 270 then (if i < 261 then (if i < 256 then (if i < 254 then (if i < 253 then 59398 else 60468) else (if i < 255 then 61591 else 62723)) else (if i < 258 then (if i < 257 then 63889 else 65059) else (if i < 259 then 66268 else (if i < 260 then 67475 else 68718)))) else (if i < 265 then (if i < 263 then (if i < 262 then 69996 else 71273) else (if i < 264 then 72587 else 73927)) else (if i < 267 then (if i < 266 then 75273 else 76657) else (if i < 268 then 78035 else (if i < 269 then 79501 else 80974))))) else (if i < 279 then (if i < 274 then (if i < 272 then (if i < 271 then 82443 else 83953) else (if i < 273 then 85511 else 87108)) else (if i < 276 then (if i < 275 then 88706 else 90358) else (if i < 277 then 92040 else (if i < 278 then 93707 else 95430)))) else (if i < 284 then (if i < 281 then (if i < 280 then 97196 else 98990) else (if i < 282 then 100815 else (if i < 283 then 102659 else 104551))) else (if i < 286 then (if i < 285 then 106485 else 108429) else (if i < 287 then 110467 else (if i < 288 then 112489 else 114154)))))))))
def smallLength : ℕ := 114154

def offsetCheck : Bool :=
  blockOffset 0==prefixLength && blockOffset blockLength==smallLength &&
    (List.range blockLength).all (fun i => decide (0 < (blockControl i).count) &&
      (blockOffset (i+1)==blockOffset i+(blockControl i).count))

theorem offset_certificate : offsetCheck=true := by decide +kernel

lemma offset_facts : blockOffset 0=prefixLength ∧ blockOffset blockLength=smallLength ∧
    ∀ i,i < blockLength → 0 < (blockControl i).count ∧
      blockOffset (i+1)=blockOffset i+(blockControl i).count := by
  have hh := offset_certificate
  simpa only [offsetCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range,
    decide_eq_true_eq,and_assoc] using hh

lemma block_offset_zero : blockOffset 0=prefixLength := offset_facts.1
lemma block_offset_last : blockOffset blockLength=smallLength := offset_facts.2.1
lemma block_count_pos (i : ℕ) (hi : i < blockLength) : 0 < (blockControl i).count :=
  (offset_facts.2.2 i hi).1
lemma block_offset_succ (i : ℕ) (hi : i < blockLength) :
    blockOffset (i+1)=blockOffset i+(blockControl i).count := (offset_facts.2.2 i hi).2

lemma block_offset_strictMono : StrictMono (fun i : Fin (blockLength+1) => blockOffset i.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change blockOffset i.val < blockOffset (i.val+1)
  rw [block_offset_succ i.val i.isLt]
  exact Nat.lt_add_of_pos_right (block_count_pos i.val i.isLt)

lemma block_offset_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ blockLength) : blockOffset i ≤ blockOffset j :=
  block_offset_strictMono.monotone (show (⟨i,by omega⟩:Fin (blockLength+1)) ≤ ⟨j,by omega⟩ from hij)

lemma prefix_le_small : prefixLength ≤ smallLength := by
  rw [← block_offset_zero,← block_offset_last]
  exact block_offset_mono (Nat.zero_le _) le_rfl

lemma exists_adjacent_interval (f : ℕ → ℕ) (N x : ℕ) (h0 : f 0 ≤ x) (hN : x < f N) :
    ∃ i,i < N ∧ f i ≤ x ∧ x < f (i+1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hprev : x < f N
    · obtain ⟨i,hi,hlo,hhi⟩ := ih hprev
      exact ⟨i,by omega,hlo,hhi⟩
    · exact ⟨N,by omega,by omega,hN⟩

lemma small_index_block (t : ℕ) (ht0 : prefixLength ≤ t) (ht1 : t < smallLength) :
    ∃ b j,b < blockLength ∧ j < (blockControl b).count ∧ t=blockOffset b+j := by
  obtain ⟨b,hb,hlo,hhi⟩ := exists_adjacent_interval blockOffset blockLength t
    (by simpa only [block_offset_zero] using ht0) (by simpa only [block_offset_last] using ht1)
  rw [block_offset_succ b hb] at hhi
  exact ⟨b,t-blockOffset b,hb,by omega,by omega⟩

lemma block_index_bounds (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    prefixLength ≤ blockOffset b+j ∧ blockOffset b+j < smallLength := by
  have hlo := block_offset_mono (Nat.zero_le b) hb.le
  have hhi := block_offset_mono (show b+1 ≤ blockLength by omega) le_rfl
  rw [block_offset_zero] at hlo
  rw [block_offset_last,block_offset_succ b hb] at hhi
  omega

lemma block_index_unique (b d j k : ℕ) (hb : b < blockLength) (hd : d < blockLength)
    (hj : j < (blockControl b).count) (hk : k < (blockControl d).count)
    (heq : blockOffset b+j=blockOffset d+k) : b=d ∧ j=k := by
  have hbd : b=d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := block_offset_mono (show b+1 ≤ d by omega) hd.le
      rw [block_offset_succ b hb] at hm
      omega
    · have hm := block_offset_mono (show d+1 ≤ b by omega) hb.le
      rw [block_offset_succ d hd] at hm
      omega
  exact ⟨hbd,by rw [hbd] at heq; omega⟩

lemma exists_block_pair (t : ℕ) (ht0 : prefixLength ≤ t) (ht1 : t < smallLength) :
    ∃ v : ℕ×ℕ,v.1 < blockLength ∧ v.2 < (blockControl v.1).count ∧ t=blockOffset v.1+v.2 := by
  obtain ⟨b,j,hb,hj,he⟩ := small_index_block t ht0 ht1
  exact ⟨(b,j),hb,hj,he⟩

noncomputable def blockPosition (t : ℕ) : ℕ×ℕ :=
  if h : prefixLength ≤ t ∧ t < smallLength then (exists_block_pair t h.1 h.2).choose else (0,0)

lemma blockPosition_spec (t : ℕ) (ht0 : prefixLength ≤ t) (ht1 : t < smallLength) :
    (blockPosition t).1 < blockLength ∧ (blockPosition t).2 < (blockControl (blockPosition t).1).count ∧
    t=blockOffset (blockPosition t).1+(blockPosition t).2 := by
  simp only [blockPosition,dif_pos (show prefixLength ≤ t ∧ t < smallLength from ⟨ht0,ht1⟩)]
  exact (exists_block_pair t ht0 ht1).choose_spec

lemma blockPosition_eq (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    blockPosition (blockOffset b+j)=(b,j) := by
  have hbounds := block_index_bounds b j hb hj
  have hh := blockPosition_spec (blockOffset b+j) hbounds.1 hbounds.2
  have he := block_index_unique (blockPosition (blockOffset b+j)).1 b
    (blockPosition (blockOffset b+j)).2 j hh.1 hb hh.2.1 hj hh.2.2.symm
  exact Prod.ext he.1 he.2

#print axioms small_index_block
end Erdos7No9Certificate
