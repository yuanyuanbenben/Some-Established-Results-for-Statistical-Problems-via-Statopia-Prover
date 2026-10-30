# IMO 2026 Problem 6: complete mathematical guidance

Source statement: https://www.imo-official.org/assets/documents/problems/2026/2026_eng.pdf
The locked input uses zero-based indices: B = a(0) is the first term.
This is a mathematical proof to formalize, not a compiled Lean certificate.
The small-support induction below replaces the incomplete first-occurrence
and least-radical sketch from the preceding experiment.

## 1. Exact assumptions and target

Every a(n) is a natural number greater than 1. The next term a(n+1) is the
least integer greater than a(n) whose gcd with each a(j), j <= n, exceeds 1.
We must prove that there are positive natural numbers T and L such that
a(n+T) = a(n)+L for EVERY n, not merely for sufficiently large n.

Write supp(b) = {p : p is prime and p divides b}, and S(n)=supp(a(n)). Each S(n) is finite and
nonempty because a(n) > 1. Write B = a(0).

## 2. Growth, intersections, and prefix enumeration

The recurrence gives a(n+1) > a(n), hence strict monotonicity and
a(n) >= B+n by induction. In particular, a is unbounded.

For any indices i and j, gcd(a(i),a(j)) > 1: for distinct indices apply the
recurrence at the larger index, exchanging gcd arguments if necessary;
for equal indices use gcd(a(i),a(i)) = a(i) > 1. Therefore S(i) and S(j)
intersect. Indeed, a prime divisor of their gcd belongs to both supports.

We need the following PREFIX fact, not just enumeration of the eventual
globally admissible set. If

    B <= v <= a(N), and gcd(v,a(j)) > 1 for every j <= N,

then v = a(k) for some k <= N. Choose the least k with v <= a(k), which
exists since v <= a(N). If k=0, both inequalities give v=B. Otherwise
a(k-1) < v <= a(k). If v < a(k), greedy minimality supplies j <= k-1
with gcd(v,a(j))=1, contradicting prefix admissibility. Thus v=a(k).

An immediate variant is useful: if 1<v<=a(N) is prefix-admissible, either
v<B, or v occurs in the prefix. No assertion about future terms is needed.

## 3. Descent through an admissible cofactor

Fix n>=1, a prime q>B, and m with a(n)=q*m. Suppose that m is
prefix-admissible:

    gcd(m,a(j)) > 1 for every j<n.

We prove that some k<n satisfies S(k) subset S(n). Put A=a(n-1).
First m>1: m=0 contradicts a(n)>1, and m=1 contradicts prefix
admissibility at j=0. Also m<a(n), since q>1.
If A<m, m itself would be a smaller legal choice than a(n), so m<=A.

If m>=B, prefix enumeration realizes m as an earlier term a(k), and
S(k)=supp(m) subset S(n), proving the desired conclusion.

The case m<B has a precise replacement; do not assume that m is an
earlier term. Since m>=2, its powers are unbounded. Let T be the least
natural number such that A < m^(T+1). Since m<=A, T>=1, and minimality
of T gives m^T<=A. For every positive t, m divides m^t, so
gcd(m,a(j)) divides gcd(m^t,a(j)); all positive powers are prefix-admissible.
The power m^(T+1)>A is a legal next candidate, hence greedy minimality gives

    q*m = a(n) <= m^(T+1) = m^T*m.

Cancel the positive factor m to obtain q<=m^T. Consequently

    B < q <= m^T <= A.

Prefix enumeration now gives m^T=a(k) with k<=n-1. Since T>=1, the prime
divisors of m^T are exactly the prime divisors of m. Thus
S(k)=supp(m) subset S(n), as required.

In Lean, the existence of T can use Nat.find and the elementary bound
t+1 <= m^t for m>=2. This avoids logarithms or real analysis entirely.
Only inclusion of prime supports is necessary; no radical equality or
coprimality between q and m is needed in this lemma.

## 4. The central strong induction: every support contains a small support

Prove the following statement by strong induction on n:

    There exists k such that S(k) subset S(n),
    and every prime in S(k) is <= B.

The witness k in this induction statement need not be <=n. Do not introduce
that unnecessary restriction. The descent in Section 3 will nevertheless
provide an earlier index when induction must be invoked again.

If every prime in S(n) is <=B, choose k=n. Otherwise take q in S(n) with
q>B and write a(n)=q*m. Necessarily n>=1: a prime divisor of the positive
integer B cannot exceed B.

The essential step is to prove that m is prefix-admissible FROM THE
INDUCTION HYPOTHESIS. Fix any j<n. By induction at j choose k_j such that

    S(k_j) subset S(j), and every prime in S(k_j) is <=B.

By the ALL-PAIRS intersection property, S(n) and S(k_j) have a common
prime r. Thus r divides a(n)=q*m and r<=B<q. Since r and q are distinct
primes, r does not divide q. Euclid's lemma therefore gives r divides m.
Also r belongs to S(j), so r divides a(j). Hence r>=2 divides
gcd(m,a(j)), and gcd(m,a(j))>1. This holds for every j<n.

This is the missing implication in the previous draft. In a branch
assuming that m is NOT prefix-admissible, the preceding argument gives
a contradiction directly. It works whether q appeared earlier or is new;
there is no need to divide the proof into first-occurrence cases.

Now Section 3 produces an index ell<n with S(ell) subset S(n). Apply the
induction hypothesis at ell, obtaining k with small-prime support
S(k) subset S(ell). Transitivity gives S(k) subset S(n), completing the
strong induction.

There is no circularity: the induction hypothesis is used only at j<n
and ell<n. Although k_j may be any index, its intersection with S(n)
follows from the previously established all-pairs gcd property, which
does not depend on this induction.

## 5. Finiteness of the actual minimal supports

Let Phi={S(n): n is natural}, and let Mm be its inclusion-minimal members:

    M in Mm iff M in Phi and for every N in Phi,
    N subset M implies M subset N.

If M=S(n) is minimal, Section 4 provides an actual support S(k) subset M
using only primes <=B. Minimality gives M subset S(k), hence M=S(k).
Therefore every member of Mm is contained in the finite set

    P={p : p is prime and p<=B}.

It follows that the union of Mm is contained in P, and Mm is finite as
a subfamily of the finite powerset of P. This proves all three conjuncts
of the previously stalled child statement, with no additional hypotheses.

Every S(n) contains a minimal actual support: consider all actual supports
contained in S(n), a nonempty collection since it contains S(n), and
choose one of least cardinality. Any proper actual subsupport would have
smaller cardinality, a contradiction. Thus F=Mm is a finite family of
nonempty ACTUAL term supports, and every S(n) contains some M in F.

For a shorter implementation of the main theorem, one may instead choose
F to be all actual supports contained in P. Section 4 already shows this
finite family covers every S(n); minimality is not essential downstream.
If a DAG node explicitly promises minimality, however, prove it as above
rather than silently changing that node's statement.

## 6. A periodic admissibility condition

Define V={b : b>1 and gcd(b,a(n))>1 for every n}. For b>1, membership in V
is equivalent to supp(b) intersecting every M in F. The forward
direction uses that each M is an actual support. Conversely, choose
M subset S(n) for each n; a common prime of b and M divides b and a(n).

Let U be the union of the finite family F and put L=product of p in U.
Every member of U is prime, so L>0, and each p in U divides L. (Even the
empty-product convention would give a positive L.) For any natural b and
p in U, p divides b+L if and only if p divides b. Thus for every b>=B,

    b in V iff b+L in V.

Both b and b+L exceed 1 since B>1. Keep this lower-bound condition when
using translation backwards; do not assert unrestricted equivalence of
membership for b=0 or b=1.

## 7. Exact enumeration and periodicity from the first term

Every a(n) belongs to V by the all-pairs gcd property. Conversely, if
b>=B lies in V, choose the least k with b<=a(k), using unboundedness.
As in Section 2, either k=0 and b=B, or greedy minimality rules out
a(k-1)<b<a(k). Thus b=a(k). The sequence is exactly the increasing
enumeration of V above B.

Since B is in V, translation gives B+L in V. Enumeration provides T with
a(T)=B+L. As L>0, strict monotonicity implies T>0.

We prove a(n+T)=a(n)+L by ordinary induction. The n=0 case is the choice
of T. Suppose the identity holds for n and set x=a(n+1)+L. Translation
gives x in V, and x>a(n)+L=a(n+T). Therefore x occurs in the sequence
after index n+T, so y=a(n+T+1)<=x.

If y<x, set b=y-L. Since y>a(n)+L, natural subtraction gives b>a(n)>=B
and y=b+L. Backwards translation gives b in V. The inequality y<x also
gives b<a(n+1). This contradicts exact enumeration (or directly greedy
minimality) because a(n)<b<a(n+1). Hence y=x. Reassociate the indices
n+T+1=(n+1)+T to finish the induction.

This establishes the required positive T,L and equality at every index.

## 8. Formalization boundaries and pitfalls

- Retain the locked IsValidSeq and target statement exactly.
- The guide's mathematical arguments still require Lean proofs; they are
  not axioms, assumptions, or already-verified dependency receipts.
- Explicit intermediate sorry holes are acceptable local checkpoints only.
  No candidate may be published or declared proved until all required
  proof and integrity gates succeed without sorryAx or other bypasses.
- Do not identify an arbitrary minimal support containing p with the
  support at p's first occurrence. No such equality has been proved.
- Do not assume that an inclusion-minimal subsupport retains a designated
  prime. Section 4 avoids that invalid inference entirely.
- Do not use rad(u*v)=rad(u)*rad(v) without coprimality, or claim an
  infinite descent without constructing a strictly smaller valid witness.
- The crucial reusable obligations are prefix enumeration, admissible
  cofactor descent, and the small-support induction. Routine powerset
  finiteness and enumeration bridges may remain local.
