# IMO 2026 Problem 2: mathematical proof guide

## Exact target and scope

Prove `main_theorem` with the published Lean hypotheses. In particular,
`K` lies strictly inside triangle `BMC`, `L` lies strictly inside triangle
`BNC`, `K` lies inside the angle `LBA`, and `L` lies inside the angle `ACK`.
The official wording says that `K` is inside triangle `ABL` and `L` inside
triangle `AKC`, whereas the published Lean statement expresses these two
conditions as strict angle-interior predicates at `B` and `C`. When using the
official picture, verify the required equivalence from the other strict
interior assumptions; do not silently replace one formulation by the other.
The three equalities of ordinary (non-directed) angles are all needed. The
conclusion is `dist O M = dist O N` for *any* point `O` equidistant from
`A,K,L`. Do not replace this by a stronger claim about a specific chosen
circumcenter, add a generic-position hypothesis, or assume the conclusion.

The guide below supplies mathematics, not a Lean proof or pre-certified
helper theorem. The engine must establish each auxiliary lemma and may choose
a different sound route. The important invariant is equality of squared
distances; take square roots only after proving both sides are nonnegative.

## 1. Strict geometry and the two traces on the sides

Set `M=(A+B)/2` and `N=(A+C)/2`. Noncollinearity of `A,B,C` makes these
midpoint identities unambiguous. Since `K` is strictly inside `BMC`, its
ray from `B` meets the open side `AC` at a unique point `Y`; write

    Y = A + s (C-A),        0 < s < 1,        B,K,Y collinear.

Likewise the ray `CL` meets the open side `AB` at a unique point `X`:

    X = A + t (B-A),        0 < t < 1,        C,L,X collinear.

These statements follow by expanding the positive barycentric witnesses in
`InsideTriangle`. Keep their positivity and ray ordering. Ordinary-angle
equalities require both the equal-angle and supplementary-angle branches;
neither `s>1/2` nor `t>1/2` is guaranteed. The two `InsideAngle` hypotheses
also supply strict ray-order information. At `s=1/2` or `t=1/2`, use a
repeated-root (tangent) argument, not division by the vanishing separation.

Write `b2=dist A C ^ 2` and `c2=dist A B ^ 2`. Both are positive. The first
angle equality `angle K B A = angle A C L`, together with the ray identities,
gives the equal-inscribed-angle criterion for the circle through `B,C,X,Y`.
Its power at `A`, calculated along the two side lines, is

    dist A B * dist A X = dist A C * dist A Y.

Since `dist A X=t*dist A B` and `dist A Y=s*dist A C`, the exact scalar
identity needed later is

    c2*t = b2*s.                                      (E)

One may instead prove (E) directly with the sine rule in the two triangles
defined by `X,Y`. Either route must justify the angle orientation using the
strict interior/ray-order assumptions.

## 2. Circle powers as affine differences

For a circle with center `U` and squared radius `r2`, define its power at a
point `P` by `Q(P)=dist P U ^ 2-r2`. When two circles have power functions
`Q1,Q2`, their difference is affine in `P`: expanding squared norms cancels
the common `inner P P` term. Consequently, on a segment
`P=(1-a) A+a C`, one has

    (Q1-Q2)(P)=(1-a)*(Q1-Q2)(A)+a*(Q1-Q2)(C).

This is the only radical-axis principle required. It remains valid when a
line is tangent to one of the circles. A second elementary lemma is the
secant-power formula: if a circle meets a directed line at parameters
`u,v`, its power at a point with parameter `z` is the product of the two
signed distances, or `length(lineDirection)^2*(z-u)*(z-v)` in affine
coordinates. Repeated roots give the tangent formula and must not be
discarded as a degenerate case.

## 3. The two angle-generated circles

The second angle equality, `angle L B K = angle L N C`, gives the circle
`Omega2` through `B,L,N,Y`; the third, `angle L C K = angle B M K`, gives
`Omega3` through `C,K,M,X`. Here is the essential ordinary-angle case split.
Since `BK` points along `BY`, if `s>1/2`, then `NY` points along `NC`, so
`angle LBY = angle LNY`. If `s<1/2`, then `NY` points opposite `NC`, so
`angle LBY + angle LNY = pi`. The first relation is the same-segment form
of the circle criterion and the second is its opposite-vertices form. In
each branch establish the requisite side-of-chord order from the strict
interior hypotheses before applying that criterion; merely equating
unoriented angles without the side information is insufficient. For
`Omega3`, `CL` points along `CX`; if `t>1/2`, `MX` points along `MB`, giving
`angle KCX = angle KMX`; if `t<1/2`, `MX` points opposite `MB`, giving
`angle KCX + angle KMX = pi`. Apply the corresponding same-segment or
opposite-vertices criterion, again with the side-of-chord order checked.
One way to discharge both side checks is to take affine coordinates with
`A=0`, `B=b`, `C=c`, write `K=(1-u)b+u*s*c` and
`L=v*t*b+(1-v)c`, and use the positive barycentric coefficients. The
strict angle hypotheses imply `1-s-v*(1-s*t)>0` and
`1-t-u*(1-s*t)>0`. Relative to the oriented chord `LY`, `B` has sign
`-(1-s-v*(1-s*t))`, while `N` has sign `v*t*(1/2-s)`. Relative to `KX`,
`C` has sign `1-t-u*(1-s*t)`, while `M` has sign `u*s*(t-1/2)`.
These signs give exactly the required side relation in each branch; the
inequalities must be derived from the hypotheses, not added as assumptions.
At `Y=N` or `X=M` the four-point criterion has a repeated point. Derive
the line-circle tangency from the same angle equality using the
tangent-chord criterion, then use the repeated-root secant-power formula.
The circle-power claims below are obligations in *all* these branches,
not a generic-position shortcut.

The only powers of these circles needed in the rest of the proof are

    Omega3: Q3(A)=c2*t/2, Q3(B)=c2*(1-t)/2, Q3(C)=0;
    Omega2: Q2(A)=b2*s/2, Q2(B)=0, Q2(C)=b2*(1-s)/2.

For example, `Omega3` meets `AB` at `M` (parameter 1/2 from `A`) and `X`
(parameter `t` from `A`), and it contains `C`. Thus
`Q3(A)=AM*AX=c2*t/2` and `Q3(B)=BM*BX=c2*(1-t)/2`. The analogous calculation
for `Omega2` uses `N,Y` on `AC` and its point `B`. These identities are valid
at a repeated intersection because the product simply becomes a square.

## 4. A circle through A that also contains K and L

Let `S` be the midpoint of `BX`, and `T` the midpoint of `CY`. They lie in
the open segments `AB` and `AC`; hence `A,S,T` are noncollinear. Let `Gamma`
be their unique circle, with power `Q`. The secant-power formula gives

    Q(A)=0,
    Q(B)=BA*BS=c2*(1-t)/2,
    Q(C)=CA*CT=b2*(1-s)/2.                    (P)

Compare `Omega3` with `Gamma`. Their powers agree at `B`. At `Y`, using
`Y=(1-s)A+s C`, affine interpolation and (E) give

    (Q3-Q)(Y)
      = (1-s)*c2*t/2 - s*b2*(1-s)/2
      = (1-s)*(c2*t-b2*s)/2 = 0.

Thus their power difference vanishes on the whole line `BY`, including `K`.
Since `K` lies on `Omega3`, `Q3(K)=0`, and hence `Q(K)=0`. No global theorem
about four radical axes is needed.

Similarly, compare `Omega2` with `Gamma`. Their powers agree at `C`. At
`X=(1-t)A+t B`, the difference is

    (Q2-Q)(X)
      = (1-t)*b2*s/2 - t*c2*(1-t)/2
      = (1-t)*(b2*s-c2*t)/2 = 0.

Their difference vanishes on `CX`, which contains `L`. Therefore `Q(L)=0`.
We have proved that `A,K,L` lie on `Gamma`. This can be implemented without
ever naming a geometric circle: construct an affine-quadratic function whose
zeros are `A,S,T`, then show its values at `K,L` are zero by the displayed
interpolation equations.

## 5. Transfer to the supplied circumcenter O

The hypothesis `IsCircumcentre A K L O` says the squared-distance power
function

    QO(P)=dist O P ^ 2-dist O A ^ 2

vanishes at `A,K,L`. The circle `Gamma` also passes through these three
points. Prove `A,K,L` are noncollinear from the strict interior/ray ordering
and the side traces; then uniqueness of the circle through three
noncollinear points yields `QO=Q`. Equivalently, the affine difference
`QO-Q` vanishes at three noncollinear points in a two-dimensional affine
space and is identically zero. Hence (P) holds with `QO` in place of `Q`.

There is also a direct algebraic way to avoid circle uniqueness. A quadratic
power function with leading term `inner P P` is determined by its values at
`A,K,L`; solve the two linear equations for its affine part. The strict
noncollinearity is the exact invertibility hypothesis. Do not conclude
uniqueness merely from the name `IsCircumcentre`.

## 6. Final midpoint calculation

Use the polarization identity along `AB` and `AC`. For any point `O`, with
`M=(A+B)/2` and `N=(A+C)/2`, direct expansion of squared distances gives

    dist O M ^ 2 - dist O N ^ 2
      = (QO(B)-QO(C))/2 - (c2-b2)/4.

Substitute the powers (P) and simplify:

    QO(B)-QO(C)
      = (c2*(1-t)-b2*(1-s))/2
      = (c2-b2)/2 - (c2*t-b2*s)/2
      = (c2-b2)/2                         by (E).

The squared-distance difference is therefore zero. Distances are
nonnegative, so `dist O M = dist O N`, exactly the published conclusion.

## Suggested honest DAG

Independent nodes may cover: the positive-barycentric trace construction;
the angle-to-cyclic-or-tangent power formulas; affine difference of power
functions; the `Gamma` transfer computation; and the final midpoint identity.
The node planner should split only where a genuine standalone theorem is
useful. The main theorem still must prove that the published angle and
interior hypotheses instantiate every auxiliary statement. In particular,
the cyclic/tangent branch and noncollinearity of `A,K,L` are proof duties,
not new assumptions.
