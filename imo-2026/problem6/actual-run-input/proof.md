# Proof

Define
\[
\mathcal S:=\{x\in\mathbb Z_{>0}:\gcd(x,a_i)>1\text{ for every }i\ge 1\}.
\]
We first relate \(\mathcal S\) to the given sequence, and then prove that \(\mathcal S\) is periodic.

## 1. The sequence enumerates \(\mathcal S\)

Any two terms of the sequence have gcd greater than \(1\): if \(i<j\), then when \(a_j\) was chosen it was required that \(\gcd(a_j,a_i)>1\). Consequently every \(a_j\) belongs to \(\mathcal S\).

The sequence is strictly increasing, hence unbounded. We claim that
\[
\{a_1,a_2,a_3,\ldots\}=\mathcal S\cap [a_1,\infty).
\tag{1}
\]
Only the reverse inclusion needs proof. Suppose that \(x\in\mathcal S\), \(x\ge a_1\), and \(x\) is not a term of the sequence. Then \(x>a_1\), and for some \(n\) we have
\[
a_n<x<a_{n+1}.
\]
Since \(x\in\mathcal S\), it satisfies \(\gcd(x,a_i)>1\) for every \(1\le i\le n\). Thus \(x\) was an admissible candidate for \(a_{n+1}\), contradicting the fact that \(a_{n+1}\) is the smallest admissible integer greater than \(a_n\). This proves (1).

For a positive integer \(x\), write
\[
\operatorname{rad}(x):=\prod_{p\mid x}p
\]
for its squarefree kernel. Because \(x\) and \(\operatorname{rad}(x)\) have exactly the same prime divisors,
\[
x\in\mathcal S\quad\Longleftrightarrow\quad \operatorname{rad}(x)\in\mathcal S.
\tag{2}
\]
Also, \(\mathcal S\) is upward closed under divisibility: if \(x\in\mathcal S\) and \(x\mid y\), then \(y\in\mathcal S\).

We shall use the following two consequences of the greedy rule.

### Lemma 1
Any two elements of \(\mathcal S\) have gcd greater than \(1\).

#### Proof
Suppose, to the contrary, that \(x,y\in\mathcal S\) and \(\gcd(x,y)=1\). Choose a positive integer \(k\) such that
\[
k\equiv 1\pmod y
\qquad\text{and}\qquad
kx\ge a_1.
\]
Since \(x\in\mathcal S\) and \(x\mid kx\), we have \(kx\in\mathcal S\). By (1), \(kx\) is therefore one of the terms \(a_i\). Since \(y\in\mathcal S\), this implies \(\gcd(y,kx)>1\). On the other hand,
\[
\gcd(y,k)=1\quad\text{and}\quad \gcd(y,x)=1,
\]
so \(\gcd(y,kx)=1\), a contradiction. ∎

### Lemma 2
If \(x>a_1\) and \(x\notin\mathcal S\), then there is a term \(a_i<x\) such that \(\gcd(x,a_i)=1\).

#### Proof
By (1), \(x\) is not a term of the sequence. Hence there is an \(n\) such that
\[
a_n<x<a_{n+1}.
\]
If \(x\) had gcd greater than \(1\) with every \(a_i\), \(1\le i\le n\), then it would be an admissible candidate for \(a_{n+1}\), contrary to the minimality of \(a_{n+1}\). Thus \(\gcd(x,a_i)=1\) for some \(i\le n\), and then \(a_i\le a_n<x\). ∎

## 2. Minimal divisibility classes in \(\mathcal S\)

Let \(\mathcal M\) be the set of all squarefree elements of \(\mathcal S\) that are minimal under divisibility. Thus \(m\in\mathcal M\) precisely when
\[
m\in\mathcal S,\qquad m\text{ is squarefree},
\]
and no proper divisor of \(m\) belongs to \(\mathcal S\).

The set \(\mathcal M\) is nonempty. Indeed, by (2), \(\operatorname{rad}(a_1)\in\mathcal S\); among the finitely many divisors of \(\operatorname{rad}(a_1)\) that belong to \(\mathcal S\), choose one minimal under divisibility.

Furthermore, every element of \(\mathcal S\) is divisible by an element of \(\mathcal M\). Indeed, for \(x\in\mathcal S\), (2) gives \(\operatorname{rad}(x)\in\mathcal S\). Choose, among the divisors of \(\operatorname{rad}(x)\) lying in \(\mathcal S\), one that is minimal under divisibility. It is squarefree and belongs to \(\mathcal M\). Therefore
\[
\mathcal S=\bigcup_{m\in\mathcal M}m\mathbb Z_{>0}.
\tag{3}
\]

The key point is that only finitely many primes can occur in members of \(\mathcal M\).

### Lemma 3 (descent lemma)
Put \(A=a_1\). If \(m\in\mathcal M\) and \(q\) is a prime divisor of \(m\), then there exists \(m'\in\mathcal M\) such that
\[
q\mid m'
\qquad\text{and}\qquad
\frac{m'}q\le A.
\tag{4}
\]

#### Proof
Start with \(m_0=m\). Suppose that \(m_j\in\mathcal M\), \(q\mid m_j\), and
\[
\frac{m_j}{q}>A.
\]
Set \(x=m_j/q\). Since \(m_j\) is minimal in \(\mathcal S\), its proper divisor \(x\) does not belong to \(\mathcal S\). Because \(x>A=a_1\), Lemma 2 supplies a term \(a_i<x\) satisfying
\[
\gcd(a_i,x)=1.
\]
By (2), \(\operatorname{rad}(a_i)\in\mathcal S\). As observed above, it is divisible by some \(m_{j+1}\in\mathcal M\). Then
\[
m_{j+1}\le \operatorname{rad}(a_i)\le a_i<x=\frac{m_j}{q}<m_j,
\tag{5}
\]
and \(\gcd(m_{j+1},x)=1\).

Both \(m_j\) and \(m_{j+1}\) lie in \(\mathcal S\), so Lemma 1 gives
\[
\gcd(m_j,m_{j+1})>1.
\]
Now \(m_j\) is squarefree and \(m_j=qx\), whereas \(m_{j+1}\) is coprime to \(x\). Hence the only possible common prime divisor of \(m_j\) and \(m_{j+1}\) is \(q\). It follows that \(q\mid m_{j+1}\).

Thus, whenever \(m_j/q>A\), we may replace \(m_j\) by a strictly smaller member \(m_{j+1}\) of \(\mathcal M\) that is still divisible by \(q\). By (5), this strictly decreasing process must terminate. At termination we obtain an \(m'\in\mathcal M\) satisfying (4). ∎

Let \(P\) be the set of primes dividing at least one member of \(\mathcal M\). We claim that \(P\) is finite. Suppose otherwise. For every \(q\in P\), Lemma 3 gives
\[
m_q=q c_q\in\mathcal M,
\qquad 1\le c_q\le A.
\tag{6}
\]
Because \(c_q\) is a proper divisor of the minimal element \(m_q\), we have \(c_q\notin\mathcal S\). There are only finitely many possible values of \(c_q\), so for some fixed \(c\in\{1,2,\ldots,A\}\),
\[
qc\in\mathcal M
\tag{7}
\]
for infinitely many distinct primes \(q\). For this fixed \(c\), we have \(c\notin\mathcal S\). By the definition of \(\mathcal S\), there is therefore some term \(a_j\) such that
\[
\gcd(c,a_j)=1.
\]
For every prime \(q\) satisfying (7), both \(a_j\) and \(qc\) belong to \(\mathcal S\). Lemma 1 yields
\[
\gcd(a_j,qc)>1.
\]
Since \(a_j\) is coprime to \(c\), this forces \(q\mid a_j\). Thus the fixed integer \(a_j\) would be divisible by infinitely many distinct primes, an impossibility. Hence \(P\) is finite.

Every member of \(\mathcal M\) is squarefree and has all its prime divisors in the finite set \(P\). Therefore \(\mathcal M\) itself is finite.

## 3. Periodicity and conclusion

Define
\[
L:=\prod_{p\in P}p.
\]
The set \(P\) is nonempty: \(\mathcal M\ne\varnothing\), while \(1\notin\mathcal S\). Thus \(L\) is a positive integer. Every \(m\in\mathcal M\) divides \(L\), and consequently (3) gives, for every positive integer \(x\),
\[
\begin{aligned}
x\in\mathcal S
&\Longleftrightarrow m\mid x\text{ for some }m\in\mathcal M\\
&\Longleftrightarrow m\mid x+L\text{ for some }m\in\mathcal M\\
&\Longleftrightarrow x+L\in\mathcal S.
\end{aligned}
\tag{8}
\]
Thus \(\mathcal S\) is periodic with period \(L\).

Let
\[
T:=\bigl|\mathcal S\cap\{1,2,\ldots,L\}\bigr|.
\]
This is positive: choose \(m\in\mathcal M\); since \(m\mid L\) and \(\mathcal S\) is upward closed under divisibility, \(L\in\mathcal S\).

By (8), every interval of \(L\) consecutive integers contains exactly \(T\) elements of \(\mathcal S\). In particular, for every \(n\), the interval
\[
(a_n,a_n+L]
\]
contains exactly \(T\) elements of \(\mathcal S\). Moreover, \(a_n+L\in\mathcal S\) by (8), so it is the last of those \(T\) elements. By (1), the sequence lists the elements of \(\mathcal S\cap[a_1,\infty)\) in strictly increasing order. Hence the \(T\)-th term after \(a_n\) is exactly \(a_n+L\). Therefore
\[
\boxed{a_{n+T}=a_n+L}
\]
for every positive integer \(n\), as required.