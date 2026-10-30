# IMO 2026 Problem 1: mathematical proof guide

This guide addresses the five conjuncts of `main_theorem` in `input.lean`.
The public `problem.lean` supplies the statements and definitions only; no
formal solution is supplied as an input. The first three conjuncts formalize
the official termination, uniqueness, and choice-independence questions.
The last two identify the terminal value by the stronger prime-exponent
formula included in the published Lean statement.

## 1. Board invariants and a strictly descending measure

Write `P(B)` for the product of all entries of a board and `N(B)` for the
number of entries strictly greater than one. Every initial entry is at least
two. A move on `m,n > 1` replaces them with

    d = gcd(m,n),       q = lcm(m,n)/d.

Both new entries are positive integers: `d >= 1`, `d | lcm(m,n)`, and
`lcm(m,n) >= d`. Thus every board reachable from an initial board has only
positive entries and still has 2026 positions. A move always preserves the
property that at least one entry exceeds one, because `lcm(m,n) > 1` and
`d*q = lcm(m,n) > 1`. In particular, `P(B) > 1` is preserved.

The product of the two selected entries is `m*n = d*lcm(m,n)`. Consequently,
writing `S` for the product of the unchanged entries,

    P(B)  = d*lcm(m,n)*S,
    P(B') =   lcm(m,n)*S.

Since `S >= 1`, `P(B') <= P(B)`, with strict inequality whenever `d > 1`.
The two selected positions contributed two to `N(B)`; their replacements
contribute at most two. If `d = 1`, they contribute exactly one: `d = 1`
while `q = lcm(m,n) = m*n > 1`. Hence `N(B') <= N(B)` always, and
`N(B') < N(B)` whenever `d = 1`. The natural-number potential

    Phi(B) = P(B) + N(B)

therefore strictly decreases at **every** move. This includes the coprime
case, where the product itself does not decrease. A proposed termination
proof using only `P(B)` is incomplete for exactly that reason.

An infinite play would give an infinite strictly descending sequence of
natural values `Phi(f k)`, which is impossible. This proves the first
conjunct. For a constructive terminal-reachability lemma, use well-founded
induction on `Phi(B)`: if `N(B) >= 2`, choose two distinct *positions* with
values greater than one, perform their move, and apply the induction
hypothesis to the smaller potential. The multiset decomposition
`B = m ::ₘ n ::ₘ s` records distinct positions even when `m = n`.

## 2. Unique large terminal entry

The positivity invariant gives `P(B') > 1` for every reachable board.
Therefore at least one entry of `B'` exceeds one (all entries are positive).
The predicate `IsTerminal B'` says that at most one does. Hence exactly one
does, proving `HasUniqueLarge B'`. All other entries of such a board equal
one, not zero: this uses the preserved positive-entry invariant. Denote the
unique large value by `M`. It follows that `B'.prod = M`.

## 3. Prime support and the exponent invariant

Fix a prime `p`. For each positive board entry `a`, let `v_p(a)` be its
ordinary nonnegative `p`-adic valuation. For the selected pair set
`r = v_p(m)`, `s = v_p(n)`. The familiar gcd/lcm identities give

    v_p(d) = min(r,s),
    v_p(q) = max(r,s) - min(r,s) = |r-s|.

Here the subtraction is in `Nat`; the equality follows from `d | lcm(m,n)`.
Euclid's algorithm yields the exact identity

    gcd(r,s) = gcd(min(r,s), max(r,s)-min(r,s)).

Taking the gcd with the valuations of every unchanged board entry preserves
this identity. Thus `gExp p B' = gExp p B` for every prime `p`. The zero
valuations from entries not divisible by `p` do **not** force the gcd to
zero: `gcd(x,0) = x`. This detail is essential to the stated `gExp`.

The finite prime support used by `Mval` is also unchanged. For any prime
`p`, divisibility of `m*n` by `p` is equivalent to divisibility of
`lcm(m,n)` by `p`, since each is equivalent to `p | m` or `p | n`.
Multiplication by the unchanged positive entries preserves this
equivalence. Hence `B.prod.primeFactors` and `B'.prod.primeFactors` contain
the same primes. Combining the support equality with the exponent equality
proves `Mval B' = Mval B` for each move, and induction on `Reachable`
proves `Mval B' = Mval B0` for every reachable board.

For Lean formalization, keep the argument local to one move before lifting
it through `Relation.ReflTransGen`. Useful independent mathematical lemmas
are (i) product/large-count descent, (ii) prime-support preservation, and
(iii) the valuation-gcd replacement identity. Ordinary multiset rewrites
and final conjunction assembly can remain in Main.

## 4. Evaluate the invariant on a terminal board

Let `B'` be reachable and terminal, with unique large entry `M`.
Every other entry is one. The valuations of `1` are zero, so for each prime
`p` the multiset gcd defining `gExp p B'` is precisely `v_p(M)`. Also
`B'.prod = M`, so the prime support in `Mval B'` is exactly the set of
prime divisors of `M`. Unique prime factorization now gives

    Mval B' = product_{p | M} p^(v_p(M)) = M.

Together with move invariance, this proves `M = Mval B0`, the fourth
conjunct. It also proves the third: two terminal boards reachable from
the same initial board both have the same unique large value `Mval B0`.
For an arbitrary natural `x`, membership with `1 < x` in either terminal
board is equivalent to `x = Mval B0`; this is the requested iff, not merely
an equality between two chosen witnesses.

Finally, terminal reachability from Section 1 supplies a terminal board,
and Section 2 supplies its entry `M > 1`. The equality above implies
`1 < Mval B0`, proving the fifth conjunct. One may instead show this
directly from prime factorization of the initial product, but the terminal
route reuses already established lemmas and avoids a second positivity
argument for the exponent product.

## Formalization cautions

- Never use any of the five claims as an axiom or an extra theorem binder;
  they are simultaneous obligations of the single target.
- Keep `Move` as a decomposition into two multiset entries. Equal values
  still correspond to distinct positions.
- The product alone is not a strict potential in the coprime case.
- Prove entry positivity before replacing a terminal board by `M` and ones;
  otherwise zero entries would invalidate that simplification.
- Do not silently replace `gExp` by a gcd of only the positive valuations
  unless the zero-valuation identity has been proved.
- Establish both the prime-support equality and exponent equality before
  claiming that `Mval` is move-invariant.
