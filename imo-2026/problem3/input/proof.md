# IMO 2026 Problem 3: a complete mathematical guide

## Target and integrity

Prove the published theorem LiuBangXiangYu.V_eq for every natural n>0, with
exactly the published definitions pieceLengths, firstPlayerShare, L,
AdmissibleMark and V. Put k=n+1, d=1/(2^k-1), c=(1+d)/2=2^n/(2^(n+1)-1).
All denominators are positive. The published file also contains unfinished
pieceLengths_sum, pieceLengths_length, L_mem_Icc, lower_bound, upper_bound.
Those declarations are removed from the approved single-target test copy
and are NOT available proved facts. Establish needed results
with honest proofs; never close V_eq by importing their sorry-backed bodies.

This is supplied mathematical guidance, not a supplied Lean proof or DAG.
The arguments below include arbitrary real cut positions, ties, repeated
lengths, fewer than n cuts, and all supremum/infimum boundedness obligations.

## 1. From marks to labelled positive pieces

Sort the distinct marks strictly increasingly and append endpoints 0 and 1.
All consecutive differences are positive; their sum telescopes to 1. There
are card(S)+1 differences. If further distinct interior marks are inserted,
each original open interval is subdivided into positive lengths summing to
its previous length. Each new mark increases the total piece count by one.
Keep a label on every new piece indicating its original interval. This
labelled refinement fact follows by inserting sorted marks one at a time,
or by grouping consecutive marks between each pair of original endpoints.
Conversely, any subdivision into positive prescribed lengths is realized
by partial sums strictly inside its original interval. These new marks are
distinct and avoid the old marks. This is the bridge between the finite
length arguments and the exact Finset/mergeSort definitions in the input.

## 2. Sorted pairing and imbalance

For a decreasing list x_1 >= ... >= x_m >= 0, append a zero when m is odd.
Let O=x_1+x_3+..., E=x_2+x_4+..., and D=O-E. Then D>=0 and
O=(sum_i x_i+D)/2. Moreover D=sum_j |x_(2j-1)-x_(2j)|.
For total length 1, the defined firstPlayerShare is (1+D)/2 and lies in
[0,1]. Sorting permutes the lengths, including their multiplicities.

Removing two equal entries from a sorted multiset leaves D unchanged.
Indeed equal entries occupy one consecutive block; deleting two changes
neither its alternating contribution nor the parity of subsequent ranks.
Consequently, if a multiset consists of equal pairs and a residual multiset
of total length R, then 0<=D<=R. Remove equal pairs successively and use
that a nonnegative sorted list has alternating sum at most its total sum.
No assertion that each equal pair occupies adjacent ranks is necessary.

The usual claiming game has this value as well: taking a largest piece
guarantees the first player at least each odd order statistic, and taking
a largest remaining piece guarantees the second at least each even one.
The Lean target already defines the first player's share by odd ranks,
so a separate extensive-form game formalization is unnecessary.

## 3. Lower bound: powers of two resist n subdivisions

Liu creates k=n+1 intervals of lengths d,2d,...,2^n d. Their sum is 1 by
the geometric-sum formula. Their n partial sums give admissible distinct
interior marks. Rescale lengths by 1/d. The initial totals are now
1,2,...,2^n, and after at most n new marks there are m<=2n+1 positive pieces.
Sort them and pair successive pieces as in Section 2. We show D>=1 at
this scale. This will imply the actual share is at least (1+d)/2.

Construct a finite undirected multigraph. Its n+1 real vertices are the
original intervals, with vertex weight 2^i. Each sorted pair creates an
edge whose endpoints are the origins of its two pieces. Allow loops and
parallel edges; they must not be silently discarded.

If m is even, there are m/2<=n edges and n+1 vertices. Some connected
component is a tree: otherwise every component has at least as many edges
as vertices, contradicting the total count. This includes an isolated
vertex as a tree, though positive original totals exclude an isolated real
vertex in this particular graph.

If m is odd, add one dummy vertex of weight 0 and pair the smallest real
piece with a dummy piece of length 0 from this vertex. There are n+2
vertices and (m+1)/2<=n+1 edges. Again some component is a tree. The dummy
has exactly one incident edge, so every tree component contains a real
vertex; in particular the selected component cannot be just the dummy.

Two-color a selected tree component with signs +1 and -1. Each edge has
opposite signs at its endpoints. Sum the signed original vertex totals.
Because every fragment at a vertex occurs in exactly one incident pair,
this signed sum is a sum, over edges of that component, of signed
differences between their two fragment lengths. Its absolute value is at
most the sum of the absolute differences on those edges, hence at most D
over all pairs. Loops cannot occur in the tree component, so they create
no exception to this identity.

On the other hand, the signed vertex sum has absolute value at least 1.
Choose the largest real vertex index r in the component. Its contribution
has magnitude 2^r, whereas all smaller indices together have total at most
1+2+...+2^(r-1)=2^r-1. The reverse triangle inequality gives a lower bound
of 1, regardless of the signs and regardless of the dummy vertex.
Thus D>=1. Undoing the scale gives D>=d and L(A,B)>=(1+d)/2 for every
admissible disjoint B. This proves the required uniform lower strategy.

The graph argument is a finite auxiliary lemma, not a new assumption about
the input. An equivalent incidence-list proof may be preferable in Lean.
Prove the tree-component counting fact with edge multiplicities, or use
the elementary fact that any finite loopless acyclic connected component
has edges=vertices-1 while a connected cyclic multigraph has edges>=vertices.

## 4. Upper bound: close subset sums and matching subdivisions

Let Liu's initial marking have q<=n+1 positive interval lengths a_1,...,a_q
summing to 1. If q<=n, Xiang bisects all q intervals. Every resulting
length occurs in an equal pair, so D=0 and L=1/2<=c. All midpoints are
strictly interior and distinct from Liu's marks.

It remains to consider q=n+1. Consider all 2^q subset sums of the a_i.
If two distinct subsets have equal sums, take their difference, giving
disjoint index sets I,J with equal total, and with I union J nonempty.
If no two subset sums coincide, arrange them increasingly. The smallest
is 0 and the largest is 1, so the 2^q-1 consecutive gaps sum to 1.
At least one gap R is <=1/(2^q-1)=d. Take its two endpoint subsets and
cancel their intersection. We obtain disjoint I,J with total difference
R in [0,d], and I union J nonempty. Exchange their names if needed so
U=sum_(i in I) a_i >= W=sum_(j in J) a_j. Thus U-W=R.

We now refine intervals indexed by I and J into equal pairs plus residual
pieces whose total is R, using at most |I|+|J|-1 extra cuts. Every remaining
original interval will be bisected, costing q-|I|-|J| further cuts. The
combined budget is at most q-1=n.

Here are full details of the refinement construction. If one group is
empty, no matching cuts are needed: the nonempty group is residual and
has total R. Bisect the complement; its size is at most q-1.
Otherwise arrange the intervals of each group in any fixed index order,
concatenating each group virtually on [0,U] and [0,W]. This does not move
physical marks; it only determines the subdivisions to be realized later.
On [0,W], superimpose the two finite sets of internal boundary positions.
Every interval in the resulting common partition has one copy on each
side, hence gives equal pairs. The portion (W,U] of the larger group
is left as residual pieces and has total length R.

At each boundary of the smaller group, including its final endpoint W
when W<U, cut the containing larger-group interval if this position is
strictly internal to it. At each internal boundary of the larger group
lying strictly inside (0,W), cut the containing smaller-group interval
if needed. Coincident existing boundaries require no cut. There are at
most |J| smaller-group positions of the first kind, and at most |I|-1
larger-group internal positions of the second kind. The total is therefore
at most |I|+|J|-1. When U=W, the final endpoint is not internal, improving
the bound. All newly created lengths are positive; zero-width cells from
coincident boundaries are omitted rather than treated as physical cuts.
Realize these subdivisions inside each original interval by partial sums.

After also bisecting the complement, all lengths outside the residual
are equal pairs. Section 2 gives D<=R<=d, hence L(A,B)<=c. The new marks
are admissible, number at most n, and disjoint from A. This proves the
upper strategy for every A, without requiring an unproved infimum-attainment
principle or allowing cuts on existing boundaries.

## 5. Passing to the exact real supremum and infimum

For each admissible A, the subtype of admissible disjoint B is nonempty:
the empty Finset is a witness. Every value L(A,B) belongs to [0,1], proved
from positivity and telescoping in Sections 1-2. Thus the corresponding
real indexed infimum is a genuine bounded infimum, with value in [0,1].
The subtype of A is also nonempty, witnessed by the empty Finset, and its
family of infima is bounded above by 1. Supply these boundedness facts
explicitly when using conditional-completeness lemmas for the real numbers.

For the geometric A constructed in Section 3 every B has L>=c; therefore
its infimum is >=c, and the supremum defining V is >=c. For every A,
Section 4 provides a particular B with L<=c; its infimum is <=c.
Taking the supremum gives V<=c. Antisymmetry yields V=c, and elementary
field algebra identifies c with the exact right-hand side of V_eq.

## Formalization boundaries

Useful independent mathematical nodes are the labelled refinement lemma,
equal-pair cancellation, the weighted finite multigraph imbalance lemma,
and the close-subset-sum matching refinement lemma. These are suggestions,
not a preassigned DAG. Do not replace the target by a certificate assuming
these claims. Handle Lean list sorting, interval placement and bounded
iSup/iInf as actual proof obligations. Main must retain every published
definition and parameter. Partial local compilations may contain explicit
sorry as work in progress, but the final theorem and dependency closure
must pass the ordinary no-hidden-sorry and integrity gates.
