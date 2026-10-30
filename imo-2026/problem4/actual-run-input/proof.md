# IMO 2026 Problem 4: complete mathematical guidance

## 1. Exact target and meaning of the game

Fix a real angle t with 0 < t < 180, measured in degrees. A valid triangle is
a multiset of three positive real angles whose sum is 180. We prove that
Mulan wins from every such triangle if and only if t = 180/n for a natural
number n >= 2. This is exactly TriangleGame.main_theorem in input.lean.
The original definitions and quantifiers are retained. In particular, a
strategy must work for BOTH children of every cut chosen by Mulan; choosing
only the favorable child is not a strategy against Shan-Yu.

Write a triangle as {a,b,c}, where a is the chosen apex and b,c are its base
angles. For c < x < 180-b, the prescribed cut has children

    L = {b, x, 180-b-x},    R = {c, 180-x, x-c}.

These are precisely IsCut's formulas. They are positive triangles: b,c are
positive; x>c>0; 180-b-x>0; x-c>0; and 180-x>b>0. Both sums are 180.
Every entry of the original triangle is <180, since the other two are positive.
The two split apex angles are u=180-b-x and v=x-c, with u+v=a. The angles
at the new point are x and 180-x. We use only these formulas, so no additional
geometric realization assumption is needed beyond the published model.

Any chosen member a of a cardinality-three multiset can be placed first in a
representation {a,b,c}; repetitions are allowed. Remove one occurrence of a,
then enumerate the remaining cardinality-two multiset. Permuting this triple
does not change the triangle. All representations below are multiset ones,
not assumptions that the angles are distinct or ordered.

## 2. A positive integral multiple of the target is already sufficient

Lemma. If a valid triangle has an angle k*t, where k is a positive natural
number, then Mulan can force a win in finitely many cuts.

Proof by induction on k, with the statement quantified over all valid
triangles. For k=1 the triangle already contains t, so use MulanWins.win.
For k>=2, present the triangle as {k*t,b,c}. Set

    x = 180-b-t.

Since k*t+b+c=180, x-c=(k-1)*t>0. Also x<180-b because t>0. Thus this is a
legal cut. Its children, after substituting x, are

    L = {b, 180-b-t, t},
    R = {c, b+t, (k-1)*t}.

The first child wins immediately; the second is a valid triangle containing
the positive integral multiple (k-1)*t, and wins by induction. MulanWins.move
therefore gives a win for the original triangle. This produces a finite
binary strategy tree, not a limit argument. Its worst branch uses at most
k-1 additional cuts. Positivity and legality have been checked before using
the inductive hypothesis on R. In Lean one can use induction on a successor
index, or strong induction on k with 1<=k; keep natural subtraction and its
real coercion explicit when k>=2.

This lemma does NOT assume 180/t is an integer. That distinction is useful
for organizing the necessity argument independently of the sufficiency one.

## 3. Sufficiency when t = 180/n

Assume n is a natural number, n>=2, and t=180/n. Thus n*t=180 and t>0.
Take an arbitrary valid triangle. If it contains t, we are done. Otherwise
we shall make a single cut for which each child has some positive integral
multiple of t, then apply Section 2 to each child.

### 3.1 The case of an angle strictly greater than t

Suppose a>t is an angle, and write the triangle as {a,b,c}. Since
180-b=c+a, the open interval (c,180-b) has length a>t. It contains a multiple
m*t of t for a positive integer m. More explicitly, choose

    m = floor(c/t) + 1.

Because c/t>=0, m is a positive natural number. The floor inequalities give
c/t<m<=c/t+1; multiplying by t>0 yields c<m*t<=c+t<c+a=180-b.
Consequently x=m*t is an admissible cut parameter. Since b>0, we also have
m*t<180=n*t, hence m<n and n-m is a positive natural number.

The left child has the angle x=m*t. The right child has the supplementary
angle 180-x=(n-m)*t. Both children are valid, and both win by Section 2.
Use MulanWins.move. The strict interval matters: choosing a multiple at an
endpoint would be illegal, which is why a>t, not merely a>=t, was used.
No limiting process or irrational approximation occurs here.

### 3.2 The case with no angle greater than t

All three angles are <=t. As we already excluded equality to t, they are
all <t. Adding gives 180<3*t. Since 180=n*t and t>0, this implies n<3.
The natural-number conditions n>=2 and n<3 force n=2, so t=90.

Choose any apex, with base angles b,c. Both b and c are <90. Set x=90=t.
Then c<x and x<180-b, so the cut is admissible. Both children contain 90:
the left contains x and the right contains 180-x. They win immediately.
Again MulanWins.move closes the strategy. This includes every acute triangle.
Right triangles were already immediate wins, and obtuse triangles were
covered by Section 3.1. There is no missing equality case at n=3: if all
angles are <=t and sum to 3*t, then equality occurs and was handled first.

Together these cases prove MulanCanGuarantee t. In fact the construction has
a uniform bound <=n-1 cuts along any branch (and one cut in the exceptional
acute n=2 case); only existence of a finite strategy is needed by the target.

## 4. An algebraic obstruction for all other target angles

For the converse it is convenient to use INTEGER multiples, allowing signed
integers as a purely algebraic device. Define

    G = { z*t : z is an integer }.

Then 0,t belong to G, and G is closed under addition and subtraction. This
is a set of reals, not an extra hypothesis on the game. Positive multiples
will be recovered at the end using t>0. Say a triangle avoids G if none of
its three angles belongs to G.

Lemma. Assume 180 does not belong to G. For any legal cut of a valid triangle
which avoids G, at least one of the two children also avoids G.

Proof. Write the parent and children using Section 1. Its angles a,b,c are
outside G. If both children had an angle in G, the left witness could not
be b and the right witness could not be c. Thus the left witness is either
x or u=180-b-x, and the right witness is either 180-x or v=x-c.
There are exactly four possibilities:

1. x and 180-x are in G. Their sum is 180, a contradiction.
2. x and v=x-c are in G. Their difference is c, contradicting that the
   parent avoids G.
3. u=180-b-x and 180-x are in G. Their difference (180-x)-u is b,
   again a contradiction.
4. u and v are in G. Their sum is 180-b-c=a, again a contradiction.

Each use of G is only closure under sum or difference. Therefore the two
children cannot both have an angle in G. At least one avoids G. Section 1
ensures the retained child is still a valid triangle.

This gives a concrete defensive invariant for Shan-Yu. Initially choose the
equilateral triangle {60,60,60}. It is valid. It avoids G: if 60=z*t, then
180=(3*z)*t would be in G, contrary to the assumption. After every cut,
retain an avoiding child given by the lemma. Such a child has no angle t,
since t=1*t belongs to G. Thus Mulan cannot force a win in finitely many cuts.

## 5. Formal finite-tree justification of the obstruction

There is no need to formalize an infinite play, a choice function, a topology,
or a well-founded relation on real angles. The published predicate MulanWins
is inductive, so the defensive invariant is proved by induction on a putative
finite winning derivation.

Fix the assumption 180 not in G. Prove that for every derivation of
MulanWins t s, if IsTriangle s, then at least one angle of s belongs to G.
Equivalently, a valid avoiding triangle cannot have such a derivation.
In the win constructor, t is an angle and t belongs to G. In the move
constructor, suppose for contradiction the parent avoids G. The cut lemma
gives a valid avoiding child. The induction hypothesis on that child's
winning derivation gives a contradiction. Notice that both child derivations
are available in MulanWins.move: we use whichever child the invariant selects.
This proves rigorously the finite-time non-guarantee claimed in Section 4.

Applying it to {60,60,60} shows

    MulanCanGuarantee t  implies  180 belongs to G.

The proof uses contraposition/classical logic only for convenient set and
finite-case reasoning; it does not assume determinacy of a different game.

## 6. Recovering the exact natural-number denominator

Suppose MulanCanGuarantee t. By Sections 4-5 there is an integer z with
180=z*t. Since t>0 and 180>0, z>0. Since also t<180, division by t shows
z=180/t>1. Thus z>=2 as an integer. Let n be its natural-number value; the
integer-to-natural conversion is valid because z>=0. We have n>=2,
the real coercion of n equals that of z, and n*t=180. Dividing by the
nonzero real number n yields t=180/n, exactly the theorem's conclusion.

Conversely a natural n>=2 satisfying t=180/n gives n*t=180 and Section 3
proves MulanCanGuarantee t. This completes both directions without changing
the locked theorem or restricting the class of initial triangles.

## 7. Formalization guidance and integrity boundaries

The useful independent mathematical components are: valid-cut preservation;
the integer-multiple winning lemma; an interval-of-length->t multiple lemma;
and the avoiding-multiples invariant. The controller may select or combine
these into its own DAG. This document is mathematical guidance, not a demand
for a fixed node count and not a preconstructed Lean proof.

For elementary multiset manipulations, retain multiplicities, use card=3 to
enumerate a triple, and derive positivity and the sum equation from IsTriangle.
For the interval lemma, either natural floors (since c/t>0) or integer floors
with an explicit nonnegativity conversion work. Do not quietly replace the
open interval by a closed one. For G, an existential integer-multiple
predicate suffices; its closure can be proved directly by ring arithmetic
instead of importing a large additive-subgroup framework.

Every appeal to an induction hypothesis on a child must carry its valid
triangle proof. The win constructor itself has no validity field, which is
why the induction statement in Section 5 is conditional on IsTriangle.
The conclusion concerns all real 0<t<180, including irrational t; no density,
rationality, continuity or regularity assumption may be added. In particular,
an argument only treating rational targets would not prove the theorem.

Only this mathematical guide and the unchanged published statement (apart
from one approved compiler-option removal) are supplied to the engine.
No published solution.lean, prior proof job, verified node, or DAG checkpoint
is supplied. Lean search, DAG construction, writers, compilation, publication
and final statement/axiom gates remain the responsibility of the Deep engine.
