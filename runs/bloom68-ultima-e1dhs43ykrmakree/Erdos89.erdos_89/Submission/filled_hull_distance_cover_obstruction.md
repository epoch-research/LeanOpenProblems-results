# Every hull distance can have a large actual cover

This is a rigorous obstruction to choosing a small-cover color from the hull,
not to the original conjecture or to an arbitrary-color cover alternative.
No EXT property of the examples is asserted. Parent checked the algebraic
construction and rectangle endpoint certificates independently.

Use the notation of extremal_distance_cover_geometry.md:
 theta_j=arctan(10^(-j)), N=prod_{j=1}^k(10^(2j)+1), R=sqrtN,
 A={prod_j(10^j+i epsilon_j):epsilon_j in{+1,-1}}, S=A union(-A).
Set H=conv S and P=H intersect Z². All2^(k+1) shell points are exposed and
there are no other points of their circle in H. Thus S is the ENTIRE hull
vertex set of P. The diameter graph is exactly the2^k antipodal matching.

For b in{-1,0,1}^k nonzero, let delta_b=Σb_j theta_j and h=|supp b|.
The shell colors are2R sin|delta_b| and2R cos|delta_b|. The estimates
 theta_j>2Σ_{r>j}theta_r, Σtheta_j<1/9
make labels unique up to b↦-b, with disjoint short/long types. Each shell
color graph is a matching of2^(k-h+1) edges.

Write alpha=prod_{j in supp b}(10^j+i b_j)=a+it and
 gamma=prod_{j notin supp b}(10^j+i). All four points gamma(±a±it) belong
toS. Their whole rectangle is contained inH, so P contains all gamma(x+iy)
with integral |x|<=a,|y|<=|t|. The long color has a matching of2|t|+1
horizontal opposite-side edges, and the short color has a matching of2a+1
vertical edges. For p=min(supp b), angle domination gives
 |t|>= (2/3)10^(Σ_{j in supp b}j-p).
For h>=2 this is>=2^(h-1); for h=1 exactly|t|=1. Alsoa>|t|. Hence every
non-diameter shell color has ACTUAL full-set cover
 tau_s(P)>=max(2^(k-h+1),2^h)>=2^((k+1)/2).
The diameter also satisfies this lower bound.

The set has n asymp N and D asymp n/sqrt(log n). For a concrete lower
cardinality bound, write prod_j(10^j+i)=u+iv and
 (10+i)prod_{j=2}^k(10^j-i)=U+iV. Then u>R/2,U>u,V>=R/16, and the rectangle
[-U,U]×[-V,V] lies inH. ThusN/8<=n<=9N and logn=k(k+1)log10+O(1).
The contained square[-floor(R/32),floor(R/32)]² realizes every sum of two
squares up to4floor(R/32)², while every distance ofP is such a norm<=4N.
Two-sided Landau bounds give the claimed sharp order with absolute constants.
Thus every complete-hull color has cover exp(Omega(sqrt(log n))), not merely
the diameter or a fixed longest prefix.

The hull-side color2u has only two edges onS, but linear cover inP. Put
d=U-u=2R sin(theta_1)sin(Σ_{j>=2}theta_j)>R/600. It is an integer withd<u.
The edges(-u+s,y)--(u+s,y), |s|<=d,|y|<=V, are all in the contained rectangle
and have disjoint endpoints. Their number(2d+1)(2V+1)>=N/2400>=n/21600.
Consequently tau_(2u)(S)=2 but tau_(2u)(P)>=n/21600. Ifj is the full-set
decreasing rank of2u, thenj<=D=O(n/sqrtlogn); the top-j graph has cover
notO(j), despite its witness being a hull side.

Relevant corpus theorem: Moric--Pritchard1103.0412/topk1-bookversion.tex,
Fact3 at lines123--133. In a STRICTLY CONVEX whole configuration, a rank<=j
chord with ell intervening vertices gives a top-j cover of size<=ell+4j+2,
by extending its short boundary interval and excluding noncrossing long
edges. That theorem cannot be transferred from the hull to the full set;
the explicit interior matching above rules out such an extension. Altman's
linear distinct-distance theorem handles sets entirely in convex position.

No claim is made about the MINIMUM cover among all colors ofP. A possible
small-cover color would have to involve interior points and be absent from
the hull palette. No actual hereditary-maximizer counterexample or proof is
established, and Spec.lean is unchanged.
