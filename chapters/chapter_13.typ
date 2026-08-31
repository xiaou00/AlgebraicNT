#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= The Riemann Zeta Function

The Riemann zeta function is the first place where the additive ordering of
the positive integers, their multiplicative factorization, and complex
analysis meet in a single object. Its Dirichlet series remembers arithmetic
functions through its coefficients, its Euler product separates the primes,
and its zeros measure the failure of primes to follow a perfectly smooth
distribution.

#quote[
  A Dirichlet series reads the integers one coefficient at a time; an Euler
  product reorganizes the same information one prime at a time.
]

== Dirichlet Series and Arithmetic Functions

=== Convergence and Holomorphy

#definition(title: "Dirichlet Series")[
  An #emph[arithmetic function] is a function

  $ a:ZZ_(>0)->CC $

  Its associated #emph[Dirichlet series] is the formal expression

  $ D_a (s):=sum_(n=1)^infinity a(n)n^(-s), quad s=sigma+i t in CC $

  Whenever the series converges, it defines a complex-valued function of
  $s$. The real number $sigma="Re"(s)$ governs the size of the terms, while
  $t="Im"(s)$ supplies the oscillation

  $ n^(-i t)=exp(-i t log n) $
]

#remark(title: "A Sparse Power Series")[
  Since $n^(-s)=exp(-s log n)$, a Dirichlet series resembles a power series
  whose frequencies are the irregularly spaced numbers $log n$. Moving to
  the right in the complex plane damps every frequency; moving vertically
  changes only its phase. This is why domains of convergence are half-planes
  rather than disks.
]

#definition(title: "Abscissae of Convergence")[
  The #emph[abscissa of convergence] $sigma_c$ and the #emph[abscissa of
  absolute convergence] $sigma_a$ are the extended real numbers characterized
  by

  $ D_a (s) " converges for " "Re"(s)>sigma_c $

  $ D_a (s) " converges absolutely for " "Re"(s)>sigma_a $

  and by failure of the corresponding type of convergence at points strictly
  to the left. Either abscissa may be $plus.minus infinity$.
]

#proposition(title: "The Half-Plane Principle")[
  If a Dirichlet series converges at $s_0$, then it converges for every
  $s$ with $"Re"(s)>"Re"(s_0)$ and converges locally uniformly in that open
  half-plane. Consequently, it is holomorphic there and may be differentiated
  term by term:

  $ D_a'(s)=-sum_(n=1)^infinity a(n)(log n)n^(-s) $

  Moreover,

  $ sigma_c<=sigma_a<=sigma_c+1 $
]

#proof[
  Put $b_n:=a(n)n^(-s_0)$. Convergence at $s_0$ means that the partial sums of
  $sum b_n$ are bounded. Abel summation applied to
  $b_n n^(-(s-s_0))$ gives convergence whenever
  $"Re"(s-s_0)>0$, uniformly when $s$ ranges over a compact subset of this
  half-plane. The locally uniform limit of holomorphic partial sums is
  holomorphic. Applying the same argument after inserting $log n$, and
  absorbing $log n$ into an arbitrarily small additional power of $n$, gives
  the derivative formula.

  Finally, convergence at $s_0$ implies that the terms
  $a(n)n^(-s_0)$ are bounded. Hence

  $ sum_n abs(a(n)n^(-s))
    <=C sum_n n^(-("Re"(s)-"Re"(s_0))) $

  which converges when $"Re"(s)>"Re"(s_0)+1$. Taking infima proves the final
  inequalities.
]

#remark(title: "Polynomial Growth Gives a First Domain")[
  If $a(n)=O(n^theta)$, then $D_a (s)$ converges absolutely for
  $"Re"(s)>theta+1$. This elementary estimate is often only the starting
  domain. Analytic continuation may later define the same function far beyond
  the region in which its original series has any meaning.
]

#proposition(title: "Abel Summation")[
  Let

  $ A(x):=sum_(n<=x) a(n) $

  If $f$ is continuously differentiable on $[1,x]$, then

  $ sum_(n<=x) a(n)f(n)
    =A(x)f(x)-integral_1^x A(t)f'(t) dif t $

  In particular,

  $ sum_(n<=x) a(n)n^(-s)
    =A(x)x^(-s)+s integral_1^x A(t)t^(-s-1) dif t $
]

#proof[
  Regard $A(t)$ as a right-continuous step function. Each jump at an integer
  $n$ is $a(n)$, so Stieltjes integration by parts gives

  $ integral_(1^-)^x f(t) dif A(t)
    =A(x)f(x)-integral_1^x A(t)f'(t) dif t $

  The integral on the left is exactly the displayed sum. Taking
  $f(t)=t^(-s)$ proves the second formula.
]

=== Dirichlet Convolution and Euler Products

#definition(title: "Dirichlet Convolution")[
  For arithmetic functions $a$ and $b$, their #emph[Dirichlet convolution] is

  $ (a ast b)(n):=sum_(d|n) a(d)b(n/d) $

  Let $delta(1)=1$ and $delta(n)=0$ for $n>1$. Then convolution is
  commutative and associative, and $delta$ is its identity.
]

#theorem(title: "Multiplication of Dirichlet Series")[
  In any half-plane where both Dirichlet series converge absolutely,

  $ D_a (s)D_b (s)=D_(a ast b)(s) $
]

#proof[
  Absolute convergence permits rearrangement of the double series:

  $ (sum_m a(m)m^(-s))(sum_n b(n)n^(-s))
    =sum_(m,n) a(m)b(n)(m n)^(-s) $

  Grouping the pairs $(m,n)$ with product $k$ gives

  $ sum_k (sum_(m|k) a(m)b(k/m))k^(-s)
    =sum_k (a ast b)(k)k^(-s) $
]

#definition(title: "Multiplicative Arithmetic Function")[
  An arithmetic function $a$ is #emph[multiplicative] if $a(1)=1$ and

  $ a(m n)=a(m)a(n) $

  whenever $gcd(m,n)=1$. It is #emph[completely multiplicative] if the same
  identity holds without the coprimality assumption.
]

#theorem(title: "Euler Product of a Multiplicative Function")[
  Suppose $a$ is multiplicative and $D_a (s)$ converges absolutely. Then

  $ D_a (s)=product_p (sum_(k=0)^infinity a(p^k)p^(-k s)) $

  where the product runs over all rational primes. If $a$ is completely
  multiplicative, this becomes

  $ D_a (s)=product_p (1-a(p)p^(-s))^(-1) $
]

#proof[
  Expanding any finite product gives precisely the terms $a(n)n^(-s)$ for
  integers whose prime factors occur in that product; unique factorization and
  multiplicativity identify the coefficient. Absolute convergence lets the
  finite set of primes tend to the set of all primes and justifies every
  rearrangement. For a completely multiplicative function, each local sum is
  a geometric series.
]

#remark(title: "Local-to-Global Information")[
  The factor

  $ sum_(k>=0) a(p^k)p^(-k s) $

  contains the entire contribution from powers of one prime $p$. The Euler
  product reconstructs the global series from these local prime-power pieces.
  This is the analytic counterpart of unique prime-ideal factorization used
  throughout the earlier chapters.
]

=== The Arithmetic Functions Encoded by $zeta$

#definition(title: "The Initial Zeta Function")[
  For $"Re"(s)>1$, the #emph[Riemann zeta function] is initially defined by

  $ zeta(s):=sum_(n=1)^infinity 1/n^s $

  It is the Dirichlet series of the constant arithmetic function
  $bold(1)(n)=1$.
]

#theorem(title: "Euler Product for the Zeta Function")[
  For $"Re"(s)>1$,

  $ zeta(s)=product_p (1-p^(-s))^(-1) $

  In particular, $zeta(s)$ has no zeros in this half-plane.
]

#proof[
  The constant function $bold(1)$ is completely multiplicative, so the Euler
  product theorem gives the formula. Moreover,

  $ sum_p abs(p^(-s))<=sum_(n>=2) n^(-"Re"(s))<infinity $

  Hence the product converges absolutely to a nonzero value.
]

#remark(title: "The Arithmetic Curve Spec Z")[
  Put $X:="Spec" ZZ$. Its codimension-one points are exactly

  $ x_p:=(p), quad p " prime" $

  and the residue field obtained from the structure sheaf is

  $ kappa(x_p)=cal(O)_(X,x_p) slash frak(m)_(x_p) tilde.eq FF_p $

  Thus the Euler product has the coordinate-free form

  $ zeta_X(s):=product_(x in X^((1)))
      (1-abs(kappa(x))^(-s))^(-1)=zeta(s) $

  In other words, the ordinary Riemann zeta function is the Hasse--Weil zeta
  function of the arithmetic curve $"Spec" ZZ$: every closed point contributes
  one local factor determined only by its residue field.

  There is also a sheaf-theoretic refinement. At closed points where $ell$ is
  invertible, an appropriate $ell$-adic sheaf $cal(F)$ replaces the scalar
  local factor by

  $ det(1-abs(kappa(x))^(-s) "Frob"_x
      | cal(F)_(overline(x)))^(-1) $

  The constant sheaf has one-dimensional stalk with trivial Frobenius and
  recovers the factors of $zeta_X$ away from $ell$; the missing local factor
  is then inserted separately. Over finite fields, the Grothendieck trace
  formula turns the closed-point product into an alternating determinant on
  étale cohomology. For $"Spec" ZZ$ the corresponding global cohomological
  picture is subtler, but the Euler product already has exactly the form
  predicted by that language.
]

#definition(title: "Möbius and von Mangoldt Functions")[
  The #emph[Möbius function] is

  $ mu(n):=cases(
      1 & n=1,
      (-1)^r quad & n " is a product of " r " distinct primes",
      0 & p^2|n " for some prime " p,
    ) $

  The #emph[von Mangoldt function] is

  $ Lambda(n):=cases(
      log p quad & n=p^k " for some prime " p " and " k>=1,
      0 & "otherwise",
    ) $
]

#proposition(title: "A Dictionary of Zeta-Generated Functions")[
  In their common half-planes of absolute convergence,

  $ 1/zeta(s)=sum_(n>=1) mu(n)n^(-s) $

  $ zeta(s)^2=sum_(n>=1) tau(n)n^(-s) $

  $ zeta(s)zeta(s-k)=sum_(n>=1) sigma_k (n)n^(-s) $

  $ zeta(s-1)/zeta(s)=sum_(n>=1) phi(n)n^(-s) $

  where

  $ tau(n):=sum_(d|n)1, quad
    sigma_k(n):=sum_(d|n)d^k $

  and $phi(n)$ is Euler's totient function. Finally, for
  $"Re"(s)>1$,

  $ -zeta'(s)/zeta(s)=sum_(n>=1) Lambda(n)n^(-s) $
]

#proof[
  The identity

  $ bold(1) ast mu=delta $

  follows by checking prime powers and using multiplicativity. It gives the
  first formula. The next two follow from

  $ tau=bold(1) ast bold(1), quad
    sigma_k=bold(1) ast "id"_k, quad "id"_k (n)=n^k $

  Euler's identity $phi="id"_1 ast mu$ gives the fourth formula.

  Taking the logarithm of the absolutely convergent Euler product yields

  $ log zeta(s)=sum_p sum_(m>=1) 1/(m p^(m s)) $

  Differentiating term by term gives

  $ -zeta'(s)/zeta(s)
    =sum_p sum_(m>=1) (log p)/p^(m s)
    =sum_n Lambda(n)n^(-s) $
]

#remark(title: "Three Views of the Same Function")[
  The series $sum n^(-s)$ treats all positive integers uniformly. The Euler
  product isolates the primes. The logarithmic derivative isolates prime
  powers and weights each of them by $log p$. For questions about the
  distribution of primes, $-zeta'/zeta$ is often the most useful of the three
  forms.
]

== Meromorphic Continuation of the Zeta Function

The series definition stops at the line $"Re"(s)=1$, but the function itself
does not. We now use the values on $"Re"(s)>1$ to construct its unique
meromorphic continuation to the whole complex plane. After this construction,
the name $zeta(s)$ will always mean the continued function, not the divergent
series outside its original half-plane.

=== A First Continuation across $"Re"(s)=1$

Define the bounded sawtooth function

$ rho(x):=x-floor(x), quad 0<=rho(x)<1 $

#proposition(title: "Integral Representation")[
  For $"Re"(s)>1$,

  $ zeta(s)=s integral_1^infinity floor(x)x^(-s-1) dif x $

  and therefore

  $ zeta(s)=s/(s-1)-s integral_1^infinity rho(x)x^(-s-1) dif x $
]

#proof[
  Apply Abel summation to $a(n)=1$, so that $A(x)=floor(x)$, and let
  $x->infinity$. When $"Re"(s)>1$, the boundary term
  $floor(x)x^(-s)$ tends to zero and gives the first identity. Substituting
  $floor(x)=x-rho(x)$ and integrating $x^(-s)$ gives the second.
]

#theorem(title: "Continuation to the Right Half-Plane")[
  The formula

  $ zeta(s):=s/(s-1)-s integral_1^infinity rho(x)x^(-s-1) dif x $

  defines a meromorphic function on $"Re"(s)>0$. It agrees with the original
  Dirichlet series on $"Re"(s)>1$ and has there only one singularity: a simple
  pole at $s=1$ with residue $1$.
]

#proof[
  Since $rho$ is bounded, the integral converges locally uniformly on
  $"Re"(s)>0$ and is holomorphic there. The term $s/(s-1)$ has a simple pole
  at $1$ with residue $1$, while the integral term is holomorphic at $1$.
  Agreement on $"Re"(s)>1$ follows from the preceding proposition.
]

#remark(title: "What Analytic Continuation Means")[
  At $s=-1$, for example, the series $sum n$ diverges and is not being
  assigned a new notion of ordinary sum. Analytic continuation says instead
  that there is a unique meromorphic function agreeing with $sum n^(-s)$
  where that series genuinely converges, and we study the value of this
  function at $s=-1$.
]

=== The Theta Function and Continuation to $CC$

#definition(title: "Jacobi Theta Function")[
  For $t>0$, define

  $ Theta(t):=sum_(n in ZZ) exp(-pi n^2 t)
    =1+2sum_(n>=1)exp(-pi n^2 t) $
]

#lemma(title: "Theta Transformation Law")[
  For every $t>0$,

  $ Theta(t)=t^(-1/2)Theta(1/t) $
]

#proof[
  The Fourier transform of the Gaussian $x mapsto exp(-pi t x^2)$ is

  $ xi mapsto t^(-1/2)exp(-pi xi^2/t) $

  Applying Poisson summation to this Gaussian gives exactly the displayed
  identity. Analytically, the transformation exchanges the small-$t$ and
  large-$t$ behavior of the same lattice sum.
]

#remark(title: "Theta as a Section on an Elliptic Curve")[
  The real-variable function above is the restriction of the holomorphic
  Jacobi theta function

  $ theta(z,tau):=sum_(n in ZZ)
      exp(pi i n^2 tau+2pi i n z), quad "Im"(tau)>0 $

  Fix $tau$ in the upper half-plane and form the complex elliptic curve

  $ E_tau:=CC slash (ZZ+tau ZZ) $

  The identities

  $ theta(z+1,tau)=theta(z,tau) $

  $ theta(z+tau,tau)
    =exp(-pi i tau-2pi i z)theta(z,tau) $

  say that $theta$ is not literally a function on $E_tau$. Its automorphy
  factor instead makes it a holomorphic section of a degree-one line bundle
  $cal(L)_theta$ on $E_tau$:

  $ theta(dot,tau) in H^0(E_tau,cal(L)_theta) $

  This space of sections is one-dimensional, so the theta section is
  canonical up to scale. Evaluating at $z=0$ and restricting to $tau=i t$
  gives $Theta(t)$. The modular isomorphism
  $E_tau tilde.eq E_(-1/tau)$ transports the theta line bundle to itself and
  yields the factor $t^(-1/2)$ in the transformation law. Thus the analytic
  continuation of zeta begins with a geometric symmetry of a family of
  complex tori.
]

#definition(title: "Completed Zeta Function")[
  Initially for $"Re"(s)>1$, put

  $ Xi_0(s):=pi^(-s/2)Gamma(s/2)zeta(s) $
]

#remark(title: "The Archimedean Point and Arakelov Completion")[
  Write

  $ Gamma_RR (s):=pi^(-s/2)Gamma(s/2) $

  The factor $Gamma_RR (s)$ is the local $L$-factor at the real place, just as
  $(1-p^(-s))^(-1)$ is the local factor at the finite place $(p)$. In the
  Arakelov picture from the preceding chapters, one formally compactifies the
  arithmetic curve by adjoining its missing infinite point:

  $ overline("Spec" ZZ):="Spec" ZZ union {infinity} $

  The completed function is then the product over #emph[all] places,

  $ Xi_0(s)=Gamma_RR (s) product_p (1-p^(-s))^(-1) $

  The gamma factor is therefore not an artificial correction appended after
  the fact. It is the archimedean local contribution required to make the
  arithmetic curve complete, and it is precisely the contribution that
  reveals the symmetry $s mapsto 1-s$.
]

#proposition(title: "Mellin Transform of the Theta Function")[
  For $"Re"(s)>1$,

  $ Xi_0(s)
    =1/2 integral_0^infinity (Theta(t)-1)t^(s/2) (dif t)/t $
]

#proof[
  Since $Theta(t)-1=2sum_(n>=1)exp(-pi n^2t)$, absolute convergence permits
  termwise integration. With $u=pi n^2t$,

  $ integral_0^infinity exp(-pi n^2t)t^(s/2) (dif t)/t
    =(pi n^2)^(-s/2)Gamma(s/2) $

  Summing over $n>=1$ proves the identity.
]

#theorem(title: "Meromorphic Continuation and Functional Equation")[
  The Riemann zeta function has a unique meromorphic continuation to $CC$.
  Its only pole is the simple pole at $s=1$, with residue $1$. The completed
  function satisfies

  $ Xi_0(s)=Xi_0(1-s) $

  Equivalently,

  $ pi^(-s/2)Gamma(s/2)zeta(s)
    =pi^(-(1-s)/2)Gamma((1-s)/2)zeta(1-s) $
]

#proof[
  Split the Mellin integral at $t=1$. In the part over $(0,1)$, substitute
  $t=1/u$ and use the theta transformation law. A direct simplification gives

  $ Xi_0(s)=1/(s(s-1))
    +1/2 integral_1^infinity (Theta(t)-1)
      (t^(s/2)+t^((1-s)/2)) (dif t)/t $

  Because $Theta(t)-1$ decays exponentially as $t->infinity$, the integral
  on the right is an entire function of $s$. This formula therefore continues
  $Xi_0$ meromorphically to $CC$, with possible simple poles only at $0$ and
  $1$. It is visibly unchanged by $s mapsto 1-s$.

  Now define

  $ zeta(s):=pi^(s/2)/Gamma(s/2) Xi_0(s) $

  away from the original half-plane. Since $1/Gamma(s/2)$ is entire and has
  simple zeros at $s=0,-2,-4,dots$, the pole of $Xi_0$ at $0$ is cancelled,
  while the pole at $1$ remains. Its residue is

  $ pi^(1/2)/Gamma(1/2)=1 $

  This gives the desired continuation. Uniqueness follows from the identity
  theorem, since any two continuations agree on $"Re"(s)>1$.
]

#definition(title: "The Riemann Zeta Function on the Complex Plane")[
  The #emph[Riemann zeta function] is the unique meromorphic function

  $ zeta:CC->CC union {infinity} $

  whose restriction to $"Re"(s)>1$ is $sum_(n>=1)n^(-s)$. Equivalently, it is
  the function constructed by the theta--Mellin continuation above. Whenever
  the defining series diverges, the notation $zeta(s)$ refers to this
  meromorphic continuation.
]

#definition(title: "Riemann's Entire Xi Function")[
  Define

  $ xi(s):=1/2 s(s-1)pi^(-s/2)Gamma(s/2)zeta(s) $

  Then $xi$ is entire and

  $ xi(s)=xi(1-s) $

  The factors $s(s-1)$ remove the two poles of the completed function. Thus
  the nontrivial zeros of $zeta$ become the zeros of an entire function with
  a particularly transparent symmetry.
]

#remark(title: "A Cohomological Reading of Xi")[
  For a smooth projective curve $C$ over $FF_q$, the étale cohomological form
  of its zeta function is

  $ Z(C,T)=
    det(1-T "Frob" | H^1_"et" (overline(C),QQ_ell))
    /((1-T)(1-q T)) $

  The factors from $H^0$ and $H^2$ create the two elementary poles; the
  determinant on the middle cohomology $H^1$ contains the interesting zeros.
  Poincaré duality on $H^1$ produces the functional equation.

  The formula

  $ xi(s)=1/2 s(s-1)Xi_0(s) $

  has exactly the same architecture. The factors $s(s-1)$ remove the two
  elementary poles, leaving an entire function whose zeros behave like a
  hypothetical middle cohomology of the compactified arithmetic curve
  $overline("Spec" ZZ)$. The symmetry $xi(s)=xi(1-s)$ then looks like a duality
  statement.

  This last sentence is a guiding analogy, not a construction of a known
  finite-dimensional cohomology theory for $"Spec" ZZ$. Producing a genuinely
  geometric or spectral object whose eigenvalues encode all nontrivial zeta
  zeros is part of the deeper geometric vision surrounding the Riemann
  hypothesis.
]

=== Special Points and Trivial Zeros

#proposition(title: "The First Continued Value and the Trivial Zeros")[
  We have

  $ zeta(0)=-1/2 $

  and, for every integer $m>=1$,

  $ zeta(-2m)=0 $

  These are simple zeros, called the #emph[trivial zeros]. There are no other
  zeros in the half-plane $"Re"(s)<0$.
]

#proof[
  Near $s=0$,

  $ Xi_0(s)=-1/s+O(1), quad
    1/Gamma(s/2)=s/2+O(s^2) $

  and $pi^(s/2)=1+O(s)$, so $zeta(0)=-1/2$.

  At $s=-2m$, the factor $1/Gamma(s/2)$ has a simple zero. The functional
  equation gives

  $ Xi_0(-2m)=Xi_0(1+2m) $

  and the value on the right is finite and nonzero because $1+2m>1$.
  Therefore $zeta$ has a simple zero at $-2m$.

  If $"Re"(s)<0$ and $s$ is not a negative even integer, then
  $1-s$ lies in $"Re"(1-s)>1$, where $zeta(1-s)$ is nonzero. The gamma factors
  in the functional equation are also finite and nonzero, so $zeta(s)$ cannot
  vanish.
]

#remark(title: "Why the Trivial Zeros Are Forced")[
  The completed function is symmetric under $s mapsto 1-s$, but
  $Gamma(s/2)$ has poles at the nonpositive even integers. Since the completed
  function is regular at $-2,-4,dots$, $zeta(s)$ must vanish there to cancel
  these gamma poles. The trivial zeros are therefore forced by the
  archimedean gamma factor.
]

== A First Analysis of the Zeros

=== The Critical Strip

#theorem(title: "Location of the Nontrivial Zeros")[
  Every zero of $zeta(s)$ is either a trivial zero $-2,-4,-6,dots$ or lies in
  the closed strip

  $ 0<="Re"(s)<=1 $

  The Euler product excludes $"Re"(s)>1$, and the functional equation excludes
  $"Re"(s)<0$ apart from the trivial zeros.
]

#remark(title: "The Remaining Boundary")[
  To replace the closed strip by the open strip $0<"Re"(s)<1$, one must also
  rule out zeros on $"Re"(s)=1$. This is substantially deeper than the
  absolute-convergence argument, and it is the decisive analytic input behind
  the prime number theorem.
]

#theorem(title: "No Zeros on the Line Re(s) = 1")[
  The Riemann zeta function has no zeros on the line $"Re"(s)=1$.
  Consequently, every nontrivial zero lies in the #emph[critical strip]

  $ 0<"Re"(s)<1 $
]

#proof[
  For $sigma>1$, the logarithm of the Euler product converges absolutely and
  gives

  $ log abs(zeta(sigma+i t))
    =sum_p sum_(m>=1) cos(m t log p)/(m p^(m sigma)) $

  The elementary inequality

  $ 3+4cos(theta)+cos(2theta)=2(1+cos(theta))^2>=0 $

  therefore implies

  $ 3log zeta(sigma)+4log abs(zeta(sigma+i t))
    +log abs(zeta(sigma+2i t))>=0 $

  Exponentiating,

  $ zeta(sigma)^3 abs(zeta(sigma+i t))^4
    abs(zeta(sigma+2i t))>=1 $

  Suppose $zeta(1+i t)=0$ for some $t!=0$, with multiplicity $m>=1$. As
  $sigma->1^+$,

  $ zeta(sigma)=O((sigma-1)^(-1)), quad
    zeta(sigma+i t)=O((sigma-1)^m) $

  while $zeta(sigma+2i t)=O(1)$ because $1+2i t$ is not the pole at $1$.
  The left side of the preceding inequality is then
  $O((sigma-1)^(4m-3))$, which tends to zero, a contradiction. At $t=0$ the
  function has a pole rather than a zero.

  The functional equation then also excludes zeros on $"Re"(s)=0$: a zero at
  $i t$ would force one at $1-i t$, while $zeta(0)=-1/2$ handles $t=0$.
]

=== Symmetries and the Critical Line

#proposition(title: "Symmetry of the Zeros")[
  If $rho$ is a nontrivial zero, then so are

  $ overline(rho), quad 1-rho, quad 1-overline(rho) $

  with the same multiplicity. Thus nontrivial zeros are symmetric about both
  the real axis and the #emph[critical line]

  $ "Re"(s)=1/2 $
]

#proof[
  The Dirichlet series has real coefficients, so
  $zeta(overline(s))=overline(zeta(s))$ first on $"Re"(s)>1$ and then
  everywhere by analytic continuation. This gives symmetry about the real
  axis. The functional equation for $xi$ gives symmetry under $s mapsto 1-s$.
]

#theorem(title: [Riemann--von Mangoldt Counting Formula])[
  Let $N(T)$ count nontrivial zeros $rho=beta+i gamma$ with
  $0<gamma<=T$, counted with multiplicity. Then

  $ N(T)=T/(2pi) log(T/(2pi))-T/(2pi)+O(log T) $

  In particular, there are infinitely many nontrivial zeros.
]

#proofsketch[
  Apply the argument principle to the completed function $xi(s)$ on a large
  rectangle containing the upper part of the critical strip. The change of
  argument of the gamma factor is evaluated using Stirling's formula; it
  contributes the two main terms displayed above. Standard bounds for
  $zeta(s)$ on the remaining edges contribute $O(log T)$. Each zero changes
  the argument by its multiplicity, which yields the formula.
]

#remark(title: "The Riemann Hypothesis")[
  The #emph[Riemann hypothesis] asserts that every nontrivial zero satisfies

  $ "Re"(rho)=1/2 $

  The functional equation explains why $1/2$ is the only possible universal
  vertical line, but symmetry alone does not force an individual zero to lie
  on it: a zero off the line could occur together with its three symmetric
  companions.
]

=== What the Zeros Measure

Define the Chebyshev function

$ psi(x):=sum_(n<=x) Lambda(n) $

It counts prime powers, weighting $p^k$ by $log p$. The logarithmic derivative
of zeta is its Dirichlet generating function, so complex analysis can recover
$psi(x)$ from $-zeta'/zeta$.

#remark(title: "The Explicit-Formula Principle")[
  Perron inversion formally begins with

  $ psi(x)=1/(2pi i) integral_(c-i infinity)^(c+i infinity)
      (-zeta'(s)/zeta(s)) x^s/s dif s, quad c>1 $

  Moving the contour to the left crosses the pole of $-zeta'/zeta$ at $s=1$
  and its poles at the zeros $rho$ of $zeta$. The residues have the schematic
  form

  $ psi(x)=x-sum_rho x^rho/rho+"smaller explicit terms" $

  The pole at $1$ supplies the smooth main term $x$; each zero supplies an
  oscillation. A zero with real part $beta$ produces a contribution of scale
  roughly $x^beta$. Thus the horizontal positions of the zeros measure the
  error in the distribution of primes.
]

#remark(title: "Möbius Cancellation and the Same Zeros")[
  Since $1/zeta(s)=sum mu(n)n^(-s)$ for $"Re"(s)>1$, zeros of $zeta$ are poles
  of the Dirichlet series that encodes the Möbius function. Put
  $M(x):=sum_(n<=x)mu(n)$. The Riemann hypothesis is equivalent to
  $M(x)=O(x^(1/2+epsilon))$ for every $epsilon>0$. Thus the same zero set
  controls cancellation in both the primes and the Möbius function.
]

== The Prime Number Theorem

The zero-free line $"Re"(s)=1$ is qualitative complex-analytic information.
The prime number theorem turns it into an asymptotic statement about a
monotone arithmetic counting function. The mechanism that permits this
passage is Tauberian: positivity prevents the coefficients from hiding large
oscillations from their transform.

=== Chebyshev Functions

#definition(title: "Prime-Counting Functions")[
  For $x>=2$, define

  $ pi(x):=sum_(p<=x)1 $

  $ theta.alt(x):=sum_(p<=x)log p $

  $ psi(x):=sum_(n<=x)Lambda(n) $

  Thus $pi(x)$ counts primes, $theta.alt(x)$ weights each prime by its
  logarithm, and $psi(x)$ also includes prime powers. Unique factorization
  gives

  $ psi(x)=sum_(1<=m<=log_2 x) theta.alt(x^(1/m)) $
]

#lemma(title: "Chebyshev Growth Bound")[
  We have

  $ theta.alt(x)=O(x), quad psi(x)=O(x) $

  and more precisely,

  $ psi(x)-theta.alt(x)=O(sqrt(x)log x) $
]

#proof[
  Every prime $p$ with $n<p<=2n$ divides the central binomial coefficient
  $binom(2n,n)$. Hence

  $ theta.alt(2n)-theta.alt(n)
    <=log binom(2n,n)
    <=log 4^n=2n log 2 $

  Summing this estimate over the dyadic intervals
  $(x/2^(j+1),x/2^j]$ gives $theta.alt(x)=O(x)$; changing endpoints to nearby
  integers contributes only a harmless $O(log x)$ term.

  Since $p^m<=x$ implies $m<=log_2 x$,

  $ psi(x)-theta.alt(x)
    =sum_(2<=m<=log_2 x) theta.alt(x^(1/m)) $

  Every summand is $O(x^(1/m))$, hence $O(sqrt(x))$, and there are
  $O(log x)$ of them. This proves the final estimate and, together with the
  bound for $theta.alt$, also gives $psi(x)=O(x)$.
]

=== The Tauberian Bridge

#theorem(title: "Wiener--Ikehara Tauberian Theorem")[
  Let $A:[1,infinity)->RR$ be nondecreasing and right-continuous, with
  $A(x)=O(x)$. Suppose its Mellin--Stieltjes transform

  $ F(s):=integral_(1^-)^infinity x^(-s) dif A(x) $

  converges for $"Re"(s)>1$. If, for some $a>=0$,

  $ F(s)-a/(s-1) $

  extends continuously to the closed half-plane $"Re"(s)>=1$ and is
  holomorphic in a neighborhood of every point of its boundary, then

  $ A(x) tilde a x $
]

#proofsketch[
  Put $x=e^u$ and introduce the positive measure

  $ dif nu(u):=e^(-u) dif A(e^u) $

  For $"Re"(z)>0$,

  $ F(1+z)=integral_0^infinity e^(-z u) dif nu(u) $

  The model $A(x)=a(x-1)$ has the same asymptotic as $a x$ and gives
  $dif nu(u)=a dif u$, so the right side is $a/z$. Altering $A$ on a bounded
  interval contributes only a holomorphic term. Thus the boundary value of
  $F(1+z)-a/z$ on $z=i t$ is the Fourier transform, in the distributional
  sense, of $dif nu-a dif u$.

  Multiply this boundary value by the compactly supported Fourier transform
  of a smooth averaging kernel. Fourier inversion and the Riemann--Lebesgue
  lemma imply that every such smoothed translate of $dif nu-a dif u$ tends to
  zero at infinity. One now chooses nonnegative upper and lower averaging
  kernels whose integrals approach $1$. The monotonicity of $A$ bounds
  $A(e^(u+h))-A(e^u)$ between the corresponding smoothed averages. Letting
  first $u->infinity$ and then $h->0$ squeezes

  $ e^(-u)A(e^u) $

  to $a$. This is $A(x)/x->a$.

  The analytic hypothesis is exactly what makes the localized boundary
  transform an ordinary continuous function; positivity and monotonicity are
  what permit the final unsmoothing. This is the Tauberian step that would be
  false for arbitrary oscillating coefficients.
]

#remark(title: "What the Tauberian Theorem Detects")[
  A simple pole $a/(s-1)$ is the transform of linear growth $a x$. The theorem
  says that if the remainder has no singularity on the boundary line, then a
  nondecreasing counting function cannot contain another term of comparable
  size. In this sense, the pole at $1$ determines the main term and boundary
  zeros would obstruct it.
]

=== Proof of the Prime Number Theorem

#theorem(title: "Prime Number Theorem")[
  As $x->infinity$,

  $ pi(x) tilde "Li"(x) tilde x/(log x) $

  where

  $ "Li"(x):=integral_2^x (dif t)/(log t) $

  Equivalently,

  $ theta.alt(x) tilde x, quad psi(x) tilde x $
]

#proof[
  We first prove the asymptotic for $psi$. Since $psi$ jumps by $Lambda(n)$ at
  each positive integer $n$, for $"Re"(s)>1$ its Mellin--Stieltjes transform
  is

  $ integral_(1^-)^infinity x^(-s) dif psi(x)
    =sum_(n>=1)Lambda(n)n^(-s)
    =-zeta'(s)/zeta(s) $

  The Chebyshev bound gives $psi(x)=O(x)$. Near $s=1$, the simple pole of zeta
  with residue $1$ gives

  $ -zeta'(s)/zeta(s)=1/(s-1)+"a holomorphic function" $

  At every other point $1+i t$ on the boundary, zeta is holomorphic and
  nonzero by the zero-free-line theorem. Therefore

  $ -zeta'(s)/zeta(s)-1/(s-1) $

  is holomorphic in a neighborhood of every point of $"Re"(s)=1$. The
  Wiener--Ikehara theorem, with $A=psi$ and $a=1$, now yields

  $ psi(x) tilde x $

  The difference between prime powers and primes is negligible: by the
  Chebyshev bound,

  $ 0<=psi(x)-theta.alt(x)=O(sqrt(x)log x)=o(x) $

  Hence $theta.alt(x) tilde x$.

  Finally, Abel summation gives

  $ pi(x)=theta.alt(x)/(log x)
    +integral_2^x theta.alt(t)/(t(log t)^2) dif t $

  The first term is asymptotic to $x/(log x)$. Since
  $theta.alt(t)=O(t)$, splitting the integral at $sqrt(x)$ shows that the
  second term is $O(x/(log x)^2)=o(x/(log x))$. Thus

  $ pi(x) tilde x/(log x) $

  A final integration by parts gives

  $ "Li"(x)=x/(log x)+O(x/(log x)^2) $

  and therefore $pi(x) tilde "Li"(x)$ as well.
]

#remark(title: "Closed Points of the Arithmetic Curve")[
  Since primes are the closed points of $"Spec" ZZ$ and
  $abs(kappa((p)))=p$, the prime number theorem can be written geometrically as

  $ abs({x in ("Spec" ZZ)^((1)) | abs(kappa(x))<=X})
    tilde "Li"(X) $
]
