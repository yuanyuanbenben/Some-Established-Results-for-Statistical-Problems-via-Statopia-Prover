# IMO 2026 Problem 5: Complete Mathematical Guide

## Source and Exact Target

Source: the official English problem sheet, day 2, problem 5:
https://www.imo-official.org/assets/documents/problems/2026/2026_eng.pdf
The PDF's second page was visually checked; in particular the left endpoint
of the inequality is a square root. A text extraction can omit that radical.

Let f map the positive real numbers into the positive real numbers, and assume
for every x,y > 0 that

    sqrt((x^2 + f(y)^2)/2) >= (f(x)+y)/2 >= sqrt(x*f(y)).          (P)

We prove the complete classification

    f(x) = x+c for all x>0, where c is a real constant and c>=0.

The proof below is a mathematical derivation prepared for this experiment,
not an already formalized solution to import. No continuity, measurability,
monotonicity, differentiability, or surjectivity of f is assumed.

The Lean input is the unchanged published AxiomMath IMO2026/Q5/problem.lean
at commit c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2. It uses
PositiveReal = {x : Real // 0 < x}, f : PositiveReal -> PositiveReal,
and the target main_theorem. Values below are coerced to real numbers when
doing algebra; function arguments and iterates remain positive subtypes.
The range positivity follows from the subtype, not an extra hypothesis.
Prove both directions of the equivalence without changing the declaration.

## 1. Equality at a Contact Point

Fix any t>0 and put q=f(t). The range condition gives q>0. Apply (P) with
x=q and y=t. Both extreme quantities become q:

    sqrt((q^2+q^2)/2) = sqrt(q^2) = q,
    sqrt(q*f(t)) = sqrt(q^2) = q.

The equalities use positivity of q; without a sign hypothesis a square root
of a square would give an absolute value. Consequently

    q >= (f(q)+t)/2 >= q.

By antisymmetry and multiplication by the positive number 2,

    f(f(t)) + t = 2*f(t),
    f(f(t)) = 2*f(t)-t.                                      (1)

This contact identity uses BOTH halves of the given inequality. It will turn
the inequality at an arbitrary pair into a sharp local comparison.

## 2. Positive Iteration Forces f(t)>=t

Fix t>0 and set d=f(t)-t. Define the forward orbit

    z_0=t,       z_(n+1)=f(z_n),       n=0,1,2,... .

Every z_n is positive. This follows by induction: z_0=t>0, and positivity of
z_n implies positivity of f(z_n)=z_(n+1). Thus (1) applies at every z_n, giving

    z_(n+2) = 2*z_(n+1)-z_n.                                  (2)

The consecutive increments are therefore constant. More explicitly,
z_1-z_0=d, and (2) gives

    z_(n+2)-z_(n+1) = z_(n+1)-z_n.

Induction proves z_(n+1)-z_n=d for every n. Summing the increments, or using
one more induction, proves

    z_n = t+n*d                                                (3)

for every nonnegative integer n, where n is regarded as a real number.
If d<0, then -d>0. By the Archimedean property choose a positive integer n
with n > t/(-d). Multiplying by -d>0 gives n*(-d)>t, hence t+n*d<0.
Equation (3) contradicts z_n>0. Therefore d>=0. Since t was arbitrary,

    f(t)>=t>0   for every t>0.                                (4)

Important: do not replace the orbit argument by an assumption that a positive
function is monotone or bounded below uniformly on its domain. Neither is
available initially. Positivity of the particular orbit is enough.

## 3. A Quadratic Bound for the Displacement

Define g(t)=f(t)-t for positive t. We now prove that for all u,v>0,

    g(v)-g(u) <= (v-u)^2/(4*f(u)).                             (5)

Let q=f(u)>0. Apply the lower inequality in (P) at x=q and y=v:

    sqrt(q*f(v)) <= (f(q)+v)/2.

By (1), f(q)=2q-u. Therefore

    sqrt(q*f(v)) <= (2q-u+v)/2.

Both sides are nonnegative: the left is a square root, and the right is also
(f(q)+v)/2, a strictly positive number. Since q*f(v)>0, squaring is legitimate
and yields

    4*q*f(v) <= (2q+v-u)^2
              = 4*q^2 + 4*q*(v-u) + (v-u)^2.

Subtract the first two terms on the right and use q=f(u):

    4*f(u)*(f(v)-f(u)-(v-u)) <= (v-u)^2,
    4*f(u)*(g(v)-g(u)) <= (v-u)^2.

Division by the positive denominator 4*f(u) proves (5). No limit and no
regularity assumption was used. Interchanging u and v also gives

    g(u)-g(v) <= (v-u)^2/(4*f(v)).                             (6)

The square on the increment is crucial. A bound merely proportional to
|v-u| would establish a Lipschitz estimate, not constancy.

## 4. Uniform Estimate on a Positive Compact Interval

Fix 0<a<b. For any u,v in [a,b], (4) gives f(u)>=u>=a and f(v)>=v>=a.
The denominators in (5) and (6) can therefore be bounded below by 4a>0:

    g(v)-g(u) <= (v-u)^2/(4a),
    g(u)-g(v) <= (v-u)^2/(4a).

Equivalently,

    |g(v)-g(u)| <= (v-u)^2/(4a).                              (7)

For a division-free Lean variant, (5) first gives
4*f(u)*(g(v)-g(u)) <= (v-u)^2. If g(v)-g(u)<=0, the desired one-sided
bound is immediate because the right side is nonnegative. Otherwise multiply
f(u)>=a by the nonnegative difference, obtaining
4*a*(g(v)-g(u)) <= (v-u)^2. Repeat in the reverse direction.
This avoids using denominator-order lemmas if those are inconvenient.

## 5. Equal Subdivision Removes Every Nonzero Displacement Difference

Let n be any positive integer and set

    h=(b-a)/n,
    t_i=a+i*h,       i=0,...,n.

Then h>0, t_0=a, t_n=b, every t_i belongs to [a,b], and
t_(i+1)-t_i=h. Apply (7) to each consecutive pair and sum:

    |g(b)-g(a)|
      = |sum_(i=0)^(n-1) (g(t_(i+1))-g(t_i))|
      <= sum_(i=0)^(n-1) |g(t_(i+1))-g(t_i)|
      <= n*h^2/(4a)
      = (b-a)^2/(4a*n).                                      (8)

Every equality here is finite: the first is telescoping, and the last follows
from h=(b-a)/n with n>0. In Lean one may instead sum the two one-sided bounds
separately, avoiding absolute-value algebra entirely.

Write D=|g(b)-g(a)|. If D>0, choose a positive integer n with

    n > (b-a)^2/(4*a*D).

Since a,D,n are positive, this implies
(b-a)^2/(4*a*n)<D, contradicting (8). Hence D=0 and g(b)=g(a).
This argument proves constancy without invoking differentiation or an
unproved continuity assertion.

For arbitrary positive u,v, use the preceding argument in the order u<v or
v<u; if u=v the equality is immediate. Thus g is constant on the whole
positive half-line.

## 6. Identify the Constant and Verify Sufficiency

Take c=g(1)=f(1)-1. From (4), c>=0. From constancy, for every x>0,

    f(x)-x=c,
    f(x)=x+c.

Conversely, let c>=0 and suppose f(x)=x+c on positive arguments. Positivity
of f(x) follows from x>0. For x,y>0 put A=x and B=y+c=f(y)>0. Then

    (f(x)+y)/2 = (x+c+y)/2 = (A+B)/2.

The desired lower bound is the arithmetic-geometric mean inequality:

    ((A+B)/2)^2 - A*B = (A-B)^2/4 >= 0.

Both (A+B)/2 and sqrt(A*B) are nonnegative, so this squared comparison gives
sqrt(A*B)<=(A+B)/2. The upper bound is the root-mean-square inequality:

    (A^2+B^2)/2 - ((A+B)/2)^2 = (A-B)^2/4 >= 0.

Again both quantities being compared are nonnegative, so
(A+B)/2 <= sqrt((A^2+B^2)/2). These are exactly the two inequalities in (P).
This proves sufficiency, including c=0. Negative constants are impossible:
for instance x=-c/2>0 would make x+c=c/2<0.

## Formalization Guidance and Integrity Boundaries

Suggested meaningful obligations are the contact identity, orbit domination,
quadratic displacement bound, and finite-subdivision constancy. Their exact
decomposition should follow the planner's Lean evidence, not a mechanical
one-node-per-paragraph translation. Main must connect the obligations and
prove the reverse implication as well.

- Preserve the positive-domain range condition and BOTH inequalities.
- Do not strengthen the hypotheses with continuity, monotonicity, an iterate
  formula, or constancy of g; each of these needed facts must be proved.
- In square-root comparisons, provide nonnegativity before squaring or taking
  square roots. In divisions, keep a>0, f(u)>0, and n>0 explicit.
- Iterate positivity and the arithmetic-orbit identity must hold for all n,
  not just until a hypothetical first crossing of zero.
- In the subdivision proof, use indices 0<=i<n for edges and 0<=i<=n for
  vertices. Establish the endpoint identity t_n=b before telescoping.
- The domain and codomain are positive-real subtypes. Keep coercions explicit
  in algebra and provide positivity when constructing subdivision arguments.
