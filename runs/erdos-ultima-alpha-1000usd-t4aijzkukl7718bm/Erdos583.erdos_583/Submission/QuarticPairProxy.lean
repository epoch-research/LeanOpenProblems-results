import Submission.ShortTriangleMixedExclusion

/-! Private two-vertex proxy repairs for a pair of quartic triangle vertices. -/
namespace Erdos583QuarticPairProxyDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

structure QuarticData {V : Type*} (G : SimpleGraph V) (r x y a b c d : V) where
  rx : G.Adj r x
  xy : G.Adj x y
  ry : G.Adj r y
  xa : G.Adj x a
  xb : G.Adj x b
  yc : G.Adj y c
  yd : G.Adj y d
  ar : a ≠ r
  br : b ≠ r
  ay : a ≠ y
  byy : b ≠ y
  cr : c ≠ r
  dr : d ≠ r
  cx : c ≠ x
  dx : d ≠ x
  ab : a ≠ b
  cd : c ≠ d
  Nx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b
  Ny : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c ∨ z=d

def QuarticData.swapX {V : Type*} {G : SimpleGraph V} {r x y a b c d : V}
    (F : QuarticData G r x y a b c d) : QuarticData G r x y b a c d :=
  ⟨F.rx,F.xy,F.ry,F.xb,F.xa,F.yc,F.yd,F.br,F.ar,F.byy,F.ay,F.cr,F.dr,F.cx,F.dx,F.ab.symm,F.cd,
    fun z hz ↦ by rcases F.Nx z hz with h|h|h|h <;> tauto,F.Ny⟩

def QuarticData.swapY {V : Type*} {G : SimpleGraph V} {r x y a b c d : V}
    (F : QuarticData G r x y a b c d) : QuarticData G r x y a b d c :=
  ⟨F.rx,F.xy,F.ry,F.xa,F.xb,F.yd,F.yc,F.ar,F.br,F.ay,F.byy,F.dr,F.cr,F.dx,F.cx,F.ab,F.cd.symm,
    F.Nx,fun z hz ↦ by rcases F.Ny z hz with h|h|h|h <;> tauto⟩

lemma connected_support_add_supported_edge {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {a b : V} (ha : a ∈ G.support) (hb : b ∈ G.support) :
    SupportConnected (G ⊔ edge a b) := by
  apply hG.of_reachable_map id _ (fun u v huv ↦ (show (G ⊔ edge a b).Adj u v from Or.inl huv).reachable)
    (fun _ _ ↦ .rfl)
  rintro u ⟨v,huv⟩
  rcases huv with huv | huv
  · exact ⟨v,huv⟩
  · rcases (edge_adj a b u v).mp huv with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩ <;> assumption

lemma QuarticData.fresh_cross_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a b c d : Fin n}
    (F : QuarticData G r x y a b c d)
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (ha : a ∈ (puncture G ({x,y} : Set (Fin n))).support)
    (hc : c ∈ (puncture G ({x,y} : Set (Fin n))).support)
    (hac : a ≠ c) (hbd : b ≠ d) (hnac : ¬G.Adj a c) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let H := puncture G S ⊔ edge a c
  have hxH : x ∉ H.support := puncture_fresh_internal (T := S) (Or.inl rfl) F.xa.ne F.cx.symm
  have hyH : y ∉ H.support := puncture_fresh_internal (T := S) (Or.inr rfl) F.ay.symm F.yc.ne
  have hH : SupportConnected H := connected_support_add_supported_edge hK ha hc
  apply gallai_private_pair_proxy hsmall G H F.xy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons F.xa.symm (Walk.cons F.xy (Walk.cons F.yc Walk.nil))
  let Q := Walk.cons F.xb.symm (Walk.cons F.rx.symm (Walk.cons F.ry (Walk.cons F.yd Walk.nil)))
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,F.xa.ne.symm,F.ay,hac,F.xy.ne,F.cx.symm,F.yc.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,F.xb.ne.symm,F.br,F.byy,hbd,F.rx.ne.symm,F.xy.ne,F.dx.symm,F.ry.ne,F.dr.symm,F.yd.ne]
  apply hD.puncture_expand_restore S hac (fun he ↦ hnac he.1) P hP Q hQ
  · intro z hz hza hzc
    simpa [P,Walk.support,hza,hzc,S] using hz
  · rintro z (rfl|rfl) v hv
    · rcases F.Nx v hv with rfl | rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
    · rcases F.Ny v hv with rfl | rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
  · intro e he
    simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_left _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_left _ _⟩
  · simp [P,Q,F.rx.ne,F.ry.ne,F.xy.ne,F.xb.ne,F.yc.ne,F.yd.ne,
      F.ar,F.ay,F.byy.symm,F.ab,F.cr.symm,F.cx,F.dx.symm,F.cd,ne_comm]

lemma QuarticData.shared_cross_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a b d : Fin n}
    (F : QuarticData G r x y a b a d)
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (had : G.Adj a d) (hbd : b ≠ d) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let H := puncture G S ⊔ edge a d
  have hadK : (puncture G S).Adj a d :=
    ⟨had,by simp [S,F.xa.ne.symm,F.ay],by simp [S,F.dx,F.yd.ne.symm]⟩
  have hxH : x ∉ H.support := puncture_fresh_internal (T := S) (Or.inl rfl) F.xa.ne F.dx.symm
  have hyH : y ∉ H.support := puncture_fresh_internal (T := S) (Or.inr rfl) F.ay.symm F.yd.ne
  have hH : SupportConnected H := connected_support_add_supported_edge hK ⟨d,hadK⟩ ⟨a,hadK.symm⟩
  apply gallai_private_pair_proxy hsmall G H F.xy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons F.xa.symm (Walk.cons F.xy (Walk.cons F.yd Walk.nil))
  let Q := Walk.cons F.yc.symm (Walk.cons F.ry.symm (Walk.cons F.rx (Walk.cons F.xb Walk.nil)))
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,F.xa.ne.symm,F.ay,F.cd,F.xy.ne,F.dx.symm,F.yd.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,F.ay,F.ar,F.xa.ne.symm,F.ab,F.ry.ne.symm,F.xy.ne.symm,F.byy.symm,F.rx.ne,F.br.symm,F.xb.ne]
  apply puncture_proxy_restore_at_start S had.ne P hP Q hQ _ _ _ _ _ _ D hD
  · intro z hz hza hzd
    simpa [P,Walk.support,hza,hzd,S] using hz
  · rintro z (rfl|rfl) v hv
    · rcases F.Nx v hv with rfl | rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
    · rcases F.Ny v hv with rfl | rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
  · intro e he
    simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_left _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_left _ _⟩
  · simp [P,Q,F.rx.ne,F.ry.ne,F.xy.ne,F.xa.ne,F.xb.ne,F.yc.ne,F.yd.ne,
      F.ar,F.ay,F.byy.symm,F.ab,F.dr,F.dx,F.cd,ne_comm]
  · simp [P,F.ay,F.cd,F.dx,F.yd.ne,ne_comm]
  · simp [Q,Walk.support,F.cd.symm,F.yd.ne.symm,F.dr,F.dx,hbd.symm]

end Erdos583QuarticPairProxyDevelopment
