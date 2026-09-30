# H099 theorem contract

Version: `1.0.4`
Date: 2026-08-14

This document fixes the exact mathematical claims of the public H099 research
note. It is authoritative over informal summaries.

## 1. Radial clipping

Let \(E\) be a nonzero real normed space, let \(\tau>0\), and define

\[
C_\tau(x)=
\begin{cases}
x,&\|x\|\le\tau,\\
\tau x/\|x\|,&\|x\|>\tau.
\end{cases}
\]

Let \(1<p\le2\) and

\[
c_p=\frac{(p-1)^{p-1}}{p^p}.
\]

For \(\alpha,\beta\ge0\), define

\[
K_p(\alpha,\beta)=
\begin{cases}
\beta,&\alpha\le p\beta,\\[2mm]
c_p\dfrac{\alpha^p}{(\alpha-\beta)^{p-1}},
&\alpha>p\beta.
\end{cases}
\]

The second branch is well-defined because
\(\alpha>p\beta\) and \(p>1\) imply \(\alpha>\beta\).
The branches agree at \(\alpha=p\beta>0\). At the origin the first branch
defines \(K_p(0,0)=0\), and the second expression has continuous extension
zero but is not itself defined there.

## 2. Exact deterministic envelope

For every \(x\in E\),

\[
\boxed{
\alpha\|x-C_\tau(x)\|
+\frac{\beta}{\tau}\|C_\tau(x)\|^2
\le
K_p(\alpha,\beta)\tau^{1-p}\|x\|^p.}
\]

The constant \(K_p(\alpha,\beta)\) is the smallest uniform constant. When
\(\alpha=\beta=0\), this means the trivial optimal constant zero.
Equivalently,

\[
K_p(\alpha,\beta)
=
\sup_{r>0}
\frac{\alpha(r-1)_++\beta\min\{r,1\}^2}{r^p}.
\]

If \(\alpha>p\beta\), the unique positive maximizing radius is

\[
r_*=\frac{p(\alpha-\beta)}{\alpha(p-1)}>1.
\]

If \((\alpha,\beta)=(0,0)\), every \(r>0\) is maximizing. For nonzero
weights with \(\alpha\le p\beta\), \(r=1\) is a maximizing radius. For
\(1<p<2\), it is the unique positive maximizing radius. For \(p=2\),
exactly the radii \(0<r\le1\) are maximizing.

## 3. Stochastic envelope and exact centered constant

Let \(H\) be a nonzero real Hilbert space and let
\(X\in L^p(\Omega;H)\), where \(L^p\) is the Bochner space and all
\(H\)-valued expectations below are Bochner expectations. Put

\[
Y=C_\tau(X),\qquad m=\mathbb EX,\qquad b=\mathbb EY.
\]

Then

\[
\boxed{
\alpha\|b-m\|
+\frac{\beta}{\tau}\mathbb E\|Y-b\|^2
\le
K_p(\alpha,\beta)\tau^{1-p}\mathbb E\|X\|^p.}
\]

No centering assumption is needed for this upper bound. The constant is exact
when the supremum is taken over all admissible strongly measurable
\(H\)-valued random variables defined on arbitrary probability spaces
(equivalently, over their Borel laws concentrated on separable subspaces):

\[
\boxed{
\sup_{\substack{\mathbb EX=0\\0<\mathbb E\|X\|^p<\infty}}
\frac{
\alpha\|\mathbb EC_\tau(X)\|
+\beta\tau^{-1}
\mathbb E\|C_\tau(X)-\mathbb EC_\tau(X)\|^2
}{
\tau^{1-p}\mathbb E\|X\|^p
}
=K_p(\alpha,\beta).}
\]

Finite two-point probability spaces suffice for the sharpness constructions.
No exactness claim is made for one arbitrary fixed probability space.

The upper bound uses only

\[
\|b-m\|=\|\mathbb E(Y-X)\|
\le\mathbb E\|Y-X\|
\]

and the Hilbert variance identity

\[
\mathbb E\|Y-b\|^2
=\mathbb E\|Y\|^2-\|b\|^2.
\]

### Sharpness families

If \(\alpha\le p\beta\), the symmetric law
\(X=\pm\tau e\), with probability \(1/2\) each and \(\|e\|=1\),
attains the constant \(K_p=\beta\).

If \(\alpha>p\beta\), let \(r_*\) be as above and, for
\(0<q<1/(1+r_*)\), define the one-dimensional law

\[
X_q=
\begin{cases}
r_*\tau e,&\text{with probability }q,\\[1mm]
-\dfrac{q r_*\tau}{1-q}e,&\text{with probability }1-q.
\end{cases}
\]

Then \(\mathbb EX_q=0\), the negative atom is inside the clipping ball, and
the normalized objective converges to \(K_p(\alpha,\beta)\) as
\(q\downarrow0\).

In the second branch, the stochastic supremum is not attained by any
nonzero centered law. Equality throughout the upper-bound chain forces every
nonzero observation to have norm \(r_*\tau\). On that sphere,
\(C_\tau(X)=X/r_*\), so centering forces
\(\mathbb EC_\tau(X)=0\). The resulting normalized objective is at most
\(\beta/r_*^p\), strictly below
\([\alpha(r_*-1)+\beta]/r_*^p=K_p(\alpha,\beta)\).

## 4. Conditional version

Let \(H\) be a nonzero real Hilbert space, let \(1<p\le2\),
\(X\in L^p(\Omega;H)\), and let \(\alpha,\beta\ge0\) be deterministic.
Let \(\mathcal G\) be a sub-sigma-field, let
\(\tau:\Omega\to(0,\infty)\) be finite almost surely and
\(\mathcal G\)-measurable, and define

\[
Y=C_\tau(X),\qquad
m=\mathbb E[X\mid\mathcal G],\qquad
b=\mathbb E[Y\mid\mathcal G].
\]

Then, almost surely,

\[
\alpha\|b-m\|
+\frac{\beta}{\tau}
\mathbb E[\|Y-b\|^2\mid\mathcal G]
\le
K_p(\alpha,\beta)\tau^{1-p}
\mathbb E[\|X\|^p\mid\mathcal G].
\]

The martingale-difference version is the special case \(m=0\). Conditional
Jensen and the conditional Hilbert variance identity justify the bound.
Conditional square-integrability holds almost surely because
\(\|C_\tau(X)\|^2\le\tau^{2-p}\|X\|^p\). If global second-moment
integrability fails, the conditional variance identity is justified by
localization on \(\mathcal G\)-measurable sets where the conditional second
moments are bounded.

## 5. One-parameter form

With \(\alpha=1\) and \(\beta=\lambda\ge0\),

\[
\|x-C_\tau(x)\|
+\frac{\lambda}{\tau}\|C_\tau(x)\|^2
\le
\kappa_p(\lambda)\tau^{1-p}\|x\|^p,
\]

where

\[
\kappa_p(\lambda)=
\begin{cases}
c_p(1-\lambda)^{1-p},&0\le\lambda\le1/p,\\
\lambda,&\lambda\ge1/p.
\end{cases}
\]

For \(p=2\),

\[
\kappa_2(\lambda)=
\begin{cases}
\dfrac{1}{4(1-\lambda)},&0\le\lambda\le1/2,\\[2mm]
\lambda,&\lambda\ge1/2.
\end{cases}
\]

## 6. Companion-result map

- \((\alpha,\beta)=(1,0)\) is the sharp residual envelope used as a local
  ingredient in H100.
- \((\alpha,\beta)=(0,1)\) is the clipped-energy endpoint used in H105.
  H101 uses the center-aware extension developed in H100 rather than H099
  directly.
- \((\alpha,\beta)=(1,1)\) gives

  \[
  \|x-C_\tau(x)\|+\tau^{-1}\|C_\tau(x)\|^2
  \le\tau^{1-p}\|x\|^p.
  \]

  After a separate portfolio-specific signed comparison, this supplies the
  radial core of the strengthened H105 one-round charge.

H099 does not imply the global theorems of H100, H101, or H105.

## 7. Scope boundaries

- No worldwide-priority theorem is claimed.
- The deterministic theorem holds in normed spaces; the centered variance
  theorem is stated only in Hilbert spaces.
- No result is claimed for \(p\le1\) or \(p>2\).
- The restriction \(p\le2\) is essential when \(\beta>0\): for \(p>2\),
  the normalized energy term \(\beta r^{2-p}\) diverges as \(r\downarrow0\).
- No convergence, regret, concentration, or portfolio-wealth theorem is
  claimed.
- In the closure of the attainable set, the exposed rare-shock arc
  \(1\le r\le p/(p-1)\) contains at least one maximizing point for every
  nonzero nonnegative support direction. At the zero direction the support
  value is zero and every attainable pair maximizes. The continuation is
  dominated, and the curve is not claimed to equal the entire feasible
  bias--variance set.
- The article is a short foundational note; the individual endpoint
  inequalities are known. The candidate contribution is their exact joint
  envelope, phase boundary, stochastic sharpness, and support-function view.
