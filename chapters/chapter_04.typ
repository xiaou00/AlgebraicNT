#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Ideal Norms

Throughout this chapter, we retain the Dedekind-extension setup from Chapter
3: $A$ is a Dedekind domain with fraction field $K$, the extension $L slash K$
is finite and separable of degree $n$, and $B$ is the integral closure of $A$
in $L$. Thus $B$ is a Dedekind domain and an $A$-lattice of rank $n$.

The field norm sends elements of $L$ to elements of $K$. We now construct its
ideal-theoretic counterpart

$ "N"_(B slash A):"FracId"(B)->"FracId"(A) $

The main subtlety is that $B$ need not be free over $A$. It is only finite
projective in general, so a definition that depends on choosing a global
$A$-basis would miss precisely the cases where the class group is nontrivial.

== Module Indices

The ordinary index $[ZZ:2ZZ]=2$ measures the change of volume between two
lattices. Over a Dedekind domain the answer is not naturally a single element
of $A$, because there may be no global bases. The correct replacement is a
fractional ideal, obtained by measuring the determinant locally at every
prime.

#definition(title: "Local Module Index")[
  Let $V$ be an $r$-dimensional $K$-vector space, let $M,N subset.eq V$ be
  $A$-lattices, and let $frak(p)$ be a nonzero prime of $A$. The localized
  modules $M_(frak(p))$ and $N_(frak(p))$ are free
  $A_(frak(p))$-modules of rank $r$.

  Choose an $A_(frak(p))$-module isomorphism

  $ phi_(frak(p)):M_(frak(p))->N_(frak(p)) $

  and let $Phi_(frak(p)):V->V$ be its unique $K$-linear extension. The
  #emph[local module index] is the principal fractional
  $A_(frak(p))$-ideal

  $ [M_(frak(p)):N_(frak(p))]_(A_(frak(p))):=det(Phi_(frak(p)))A_(frak(p)) $
]

#remark(title: "Why It Is Well Defined")[
  Any two choices of $phi_(frak(p))$ differ by automorphisms of the free
  modules $M_(frak(p))$ and $N_(frak(p))$. Their determinants are units of
  $A_(frak(p))$, so they generate the same principal fractional ideal. The
  generator is not canonical, but the ideal is.
]

#definition(title: "Global Module Index")[
  The #emph[module index] of $N$ in $M$ is

  $ [M:N]_A:=inter.big_(0!=frak(p) subset.eq A) [M_(frak(p)):N_(frak(p))]_(A_(frak(p))) subset.eq K $

  where the intersection takes place inside $K$.
]

#proposition(title: "Local-to-Global Existence")[
  The module index $[M:N]_A$ is a nonzero fractional ideal of $A$, and for
  every nonzero prime $frak(p)$,

  $ ([M:N]_A)_(frak(p))=[M_(frak(p)):N_(frak(p))]_(A_(frak(p))) $
]

#proof[
  By commensurability of lattices, there is a nonzero $c in A$ such that
  $c M subset.eq N$ and $c N subset.eq M$. If $frak(p)$ does not contain $c$,
  then $c$ is a unit in $A_(frak(p))$ and
  $M_(frak(p))=N_(frak(p))$. Hence the local index is $A_(frak(p))$ away from
  the finitely many prime divisors of $(c)$.

  At each remaining prime the local index is a unique integer power of
  $frak(p)A_(frak(p))$. The product of these finitely many powers, allowing
  negative exponents, is a nonzero fractional ideal $J$ of $A$ with exactly
  the prescribed localizations. The local description of fractional ideals
  from Chapter 1 then gives $J=[M:N]_A$ and proves the claimed localization
  formula.
]

#proposition(title: "Calculus of Module Indices")[
  For $A$-lattices $M,N,P$ in the same $K$-vector space,

  $ [M:N]_A [N:P]_A=[M:P]_A $

  In particular,

  $ [M:M]_A=A, quad [M:N]_A^(-1)=[N:M]_A $

  If $N subset.eq M$, then $[M:N]_A$ is an integral ideal of $A$. If $M$ and
  $N$ are free and bases of $M$ and $N$ are related by a matrix $C in
  "Mat"_r (K)$, with the $N$-basis equal to the $M$-basis multiplied by $C$,
  then

  $ [M:N]_A=(det C) $
]

#proof[
  Localize at $frak(p)$. Isomorphisms
  $M_(frak(p))->N_(frak(p))->P_(frak(p))$ compose, and determinants multiply.
  This proves the first identity locally and hence globally. The inverse
  formulas follow immediately. If $N subset.eq M$, the change-of-basis matrix
  has entries in $A_(frak(p))$ at every prime, so every local determinant has
  nonnegative valuation; therefore the global index is integral. The free
  case is the same determinant computation before localization.
]

#definition(title: "The Geometric Module Index")[
    Put $X="Spec" A$ and suppose first that $N subset.eq M$. The corresponding
    finite projective modules give rank-$r$ vector bundles

    $ cal(E)_N:=tilde(N) -> cal(E)_M:=tilde(M) $

    with the same generic fiber $V$. Their quotient

    $ cal(Q):=cal(E)_M slash cal(E)_N $

    is a #emph[torsion coherent sheaf] supported at finitely many closed
    points. Let $X^((1))$ denote the set of codimension-one points of $X$;
    these are precisely its closed points. For $x in X^((1))$, define

    $ ell_x (cal(Q)):="length"_(cal(O)_(X,x)) (cal(Q)_x) $

    The #emph[geometric module index] is the effective divisor

    $ D_(M slash N):=sum_(x in X^((1))) ell_x (cal(Q))[x] $

    For arbitrary lattices $M,N subset.eq V$, commensurability supplies a
    common sublattice $P subset.eq M inter N$. Define the relative divisor

    $ D_(M,N):=D_(M slash P)-D_(N slash P) $

    The next theorem shows that this divisor is independent of $P$ and is an
    equivalent definition of the module index.
]

#theorem(title: "Equivalence of the Determinant and Divisor Definitions")[
  Recall the ideal--divisor isomorphism from Chapter 1,

  $ Phi(I)=sum_frak(p) v_(frak(p)) (I)[frak(p)] $

  For any two $A$-lattices $M,N subset.eq V$,

  $ Phi([M:N]_A)=D_(M,N) $

  Equivalently, the module index may be defined geometrically by

  $ [M:N]_A=Phi^(-1) (D_(M,N)) $

  In particular, if $N subset.eq M$, then

  $ v_(frak(p)) ([M:N]_A)="length"_(A_(frak(p))) (M_(frak(p)) slash N_(frak(p))) $
]

#proof[
  First suppose that $N subset.eq M$. Fix a nonzero prime $frak(p)$ and a
  uniformizer $pi$ of $A_(frak(p))$. The elementary-divisor theorem gives a
  basis $e_1,dots,e_r$ of $M_(frak(p))$ and nonnegative integers
  $a_1,dots,a_r$ such that

  $ N_(frak(p))=A_(frak(p))pi^(a_1)e_1 ⊕ dots ⊕ A_(frak(p))pi^(a_r)e_r $

  Relative to this basis, an isomorphism
  $M_(frak(p))->N_(frak(p))$ is represented by the diagonal matrix

  $ "diag"(pi^(a_1),dots,pi^(a_r)) $

  Its determinant gives

  $ v_(frak(p)) ([M:N]_A)=a_1+dots+a_r $

  On the geometric side,

  $ M_(frak(p)) slash N_(frak(p)) tilde.eq A_(frak(p)) slash (pi^(a_1)) ⊕ dots ⊕ A_(frak(p)) slash (pi^(a_r)) $

  and the length of this module is also $a_1+dots+a_r$. Thus the coefficient
  of $[frak(p)]$ in $Phi([M:N]_A)$ equals the coefficient of the corresponding
  closed point in $D_(M slash N)$. This proves the result for an inclusion.

  For general $M,N$, choose $P subset.eq M inter N$. The cocycle identity gives

  $ [M:N]_A=[M:P]_A [N:P]_A^(-1) $

  Applying $Phi$ and using the inclusion case yields

  $ Phi([M:N]_A)=D_(M slash P)-D_(N slash P)=D_(M,N) $

  The left-hand side does not depend on $P$, so neither does the relative
  divisor. This also proves that the geometric prescription is equivalent to
  the determinant definition.
]

#corollary(title: "Determinant Line, Fitting Ideal, and Degeneracy Divisor")[
  The relative determinant line of two lattices satisfies

  $ [M:N]_A cal(O)_X tilde.eq "det"(cal(E)_N) ⊗ "det"(cal(E)_M)^∨ $

  If $N subset.eq M$, then

  $ [M:N]_A="Fitt"_0 (M slash N) $

  and $D_(M slash N)$ is the vanishing divisor of the determinant of the
  inclusion $cal(E)_N->cal(E)_M$.
]

#proof[
  The statements can be checked over each DVR $A_(frak(p))$. In the diagonal
  form used above, both the relative determinant line and the zeroth Fitting
  ideal are generated by $pi^(a_1+dots+a_r)$. The determinant of the inclusion
  vanishes to this same order, proving all three claims.
]

#remark(title: "What the Divisor Remembers")[
  Locally, the integers $a_1,dots,a_r$ record the changes of scale in the
  individual vector-bundle directions. The geometric module index retains
  only their sum, which is simultaneously a determinant valuation, the length
  of a torsion quotient, and the multiplicity of a closed point in a divisor.
  For noncomparable lattices, positive coefficients record relative zeros and
  negative coefficients record relative poles.
]

#quote[
  The genuine geometric object behind the module index is the relative
  divisor measuring where, and by how much, two lattices fail to coincide.
]

#remark(title: "Rank One and the Colon Ideal")[
  When $V=K$, its lattices are precisely the nonzero fractional ideals of
  $A$. For fractional ideals $M,N$,

  $ [M:N]_A=(N:M)=N M^(-1) $

  where

  $ (N:M):={x in K | x M subset.eq N} $

  Notice the reversed order: module index generalizes $[ZZ:2ZZ]=2$, whereas a
  colon ideal behaves like a ratio.
]

#theorem(title: "Module Index from a Quotient")[
    Suppose $N subset.eq M$ and the finite torsion module $M slash N$ has a
    cyclic decomposition

    $ M slash N tilde.eq A slash I_1 ⊕ dots ⊕ A slash I_s $

    for nonzero integral ideals $I_1,dots,I_s$ of $A$. Then

    $ [M:N]_A=I_1 dots I_s $
]

#proof[
  Localize at a nonzero prime $frak(p)$ and choose a uniformizer $pi$ of the
  DVR $A_(frak(p))$. Choose bases of $M_(frak(p))$ and $N_(frak(p))$. The
  matrix expressing the latter basis in terms of the former has Smith normal
  form

  $ "diag"(pi^(d_1),dots,pi^(d_r)) $

  Its determinant has valuation $d_1+dots+d_r$. On the other hand, the
  localized cyclic decomposition shows that the same module has total length

  $ sum_(j=1)^s v_(frak(p)) (I_j) $

  Uniqueness of the invariant factors over a PID identifies these two
  integers. Thus the localizations of $[M:N]_A$ and $I_1 dots I_s$ agree at
  every prime, proving the equality.
]

#example(title: "The Classical Lattice Index")[
  Let $A=ZZ$, $M=ZZ^2$, and

  $ N=ZZ(2,0)+ZZ(1,3) $

  The change-of-basis matrix has determinant $6$, so

  $ [M:N]_ZZ=(6) $

  Correspondingly, $M slash N$ is a finite abelian group of order $6$. The
  ideal-valued module index is therefore the Dedekind-domain version of
  lattice covolume.
]

== The Ideal Norm

Every nonzero fractional $B$-ideal is an $A$-lattice in $L$, so the module
index can be applied to the pair $B,I$.

#definition(title: "Relative Ideal Norm")[
  For a nonzero fractional ideal $I$ of $B$, its #emph[ideal norm from $B$ to
  $A$] is

  $ "N"_(B slash A) (I):=[B:I]_A $

  We also set $"N"_(B slash A) ((0)):=(0)$.
]

If $I subset.eq B$ is integral, then $"N"_(B slash A) (I)$ is an integral
ideal of $A$. For a genuinely fractional ideal the norm may have negative
prime exponents, exactly as it should for a homomorphism between fractional
ideal groups.

#proposition(title: "Compatibility with the Field Norm")[
    For every $alpha in L^times$,

    $ "N"_(B slash A) (alpha B)="N"_(L slash K) (alpha)A $
]

#proof[
  At every nonzero prime $frak(p)$ of $A$, multiplication by $alpha$ gives an
  isomorphism of free $A_(frak(p))$-modules

  $ B_(frak(p))->alpha B_(frak(p)) $

  Its $K$-linear extension is multiplication by $alpha$ on $L$, whose
  determinant is $"N"_(L slash K) (alpha)$. Thus all local module indices are
  the localizations of the principal ideal
  $"N"_(L slash K) (alpha)A$.
]

#theorem(title: "Multiplicativity of the Ideal Norm")[
  For nonzero fractional ideals $I,J$ of $B$,

  $ "N"_(B slash A) (I J)="N"_(B slash A) (I)"N"_(B slash A) (J) $

  Hence $"N"_(B slash A):"FracId"(B)->"FracId"(A)$ is a group
  homomorphism.
]

#proof[
  It is enough to compare localizations at every nonzero prime $frak(p)$ of
  $A$. The semilocal Dedekind domain $B_(frak(p))$ is a PID, so there are
  $alpha,beta in L^times$ with

  $ I_(frak(p))=alpha B_(frak(p)), quad J_(frak(p))=beta B_(frak(p)) $

  The principal-ideal formula and multiplicativity of the field norm give

  $ "N"_(B_(frak(p)) slash A_(frak(p))) (I_(frak(p))J_(frak(p)))="N"_(L slash K) (alpha beta)A_(frak(p)) $

  $ ="N"_(L slash K) (alpha)"N"_(L slash K) (beta)A_(frak(p)) $

  This is the product of the two localized ideal norms. Equality at all
  $frak(p)$ proves the result.
]

#corollary(title: "Norm and Relative Module Index")[
  For nonzero fractional $B$-ideals $I$ and $J$,

  $ [I:J]_A="N"_(B slash A) (I^(-1)J)="N"_(B slash A) ((J:I)) $
]

#proof[
  The colon-ideal identity $(J:I)=I^(-1)J$ holds because every nonzero
  fractional ideal of $B$ is invertible. Using the cocycle rule for module
  indices and multiplicativity of the norm gives

  $ [I:J]_A=[I:B]_A [B:J]_A=[B:I]_A^(-1)[B:J]_A $

  $ ="N"_(B slash A) (I^(-1)J) $
]

#proposition(title: "The Norm Is Generated by Element Norms")[
    For every fractional ideal $I$ of $B$,

    $ "N"_(B slash A) (I)=("N"_(L slash K) (alpha):alpha in I) $

    where the right-hand side denotes the fractional $A$-ideal generated by
    all field norms of elements of $I$.
]

#proof[
  Localize at $frak(p)$ and write
  $I_(frak(p))=gamma B_(frak(p))$. Every element of $I_(frak(p))$ is
  $gamma b$ with $b in B_(frak(p))$, so its field norm lies in
  $"N"_(L slash K) (gamma)A_(frak(p))$. Conversely, write
  $gamma=alpha/s$ with $alpha in I$ and $s in A$, $s in.not frak(p)$. Since
  $"N"_(L slash K) (s)=s^n$ is a unit of $A_(frak(p))$, the norm of $alpha$
  generates the same localized ideal as the norm of $gamma$. The two sides
  therefore agree after localization at every prime.
]

=== Norms of Prime Ideals

Let $frak(q)$ be a nonzero prime of $B$ lying above $frak(p)$, and recall the
residue degree

$ f_(frak(q) slash frak(p))=[B slash frak(q):A slash frak(p)] $

#theorem(title: "Norm of a Prime Ideal")[
  If $frak(q)|frak(p)$, then

  $ "N"_(B slash A) (frak(q))=frak(p)^(f_(frak(q) slash frak(p))) $
]

#proof[
  As a vector space over $A slash frak(p)$, the residue field
  $B slash frak(q)$ has dimension $f=f_(frak(q) slash frak(p))$. Hence, as an
  $A$-module,

  $ B slash frak(q) tilde.eq (A slash frak(p))^f $

  Applying the quotient formula for the module index gives

  $ [B:frak(q)]_A=frak(p)^f $

  and the left-hand side is the definition of
  $"N"_(B slash A) (frak(q))$.
]

#corollary(title: "The Valuation Formula")[
  For every nonzero fractional $B$-ideal $I$ and every nonzero prime
  $frak(p)$ of $A$,

  $ v_(frak(p)) ("N"_(B slash A) (I))=sum_(frak(q)|frak(p)) f_(frak(q) slash frak(p))v_(frak(q)) (I) $

  Equivalently,

  $ "N"_(B slash A) (I)=product_frak(p) frak(p)^(sum_(frak(q)|frak(p)) f_(frak(q) slash frak(p))v_(frak(q)) (I)) $
]

#proof[
  Factor $I$ into prime ideals of $B$, apply multiplicativity, and use the
  formula for the norm of each prime factor. Only finitely many valuations are
  nonzero.
]

#proposition(title: "Ideal Norm as Pushforward of Divisors")[
  Let $pi:"Spec" B->"Spec" A$. Define the pushforward on prime divisors by

  $ pi_* [frak(q)]:=f_(frak(q) slash frak(p))[frak(p)], quad frak(p)=frak(q) inter A $

  and extend it $ZZ$-linearly. If $Phi_A$ and $Phi_B$ denote the
  ideal--divisor correspondences for $A$ and $B$, then

  $ Phi_A ("N"_(B slash A) (I))=pi_* Phi_B (I) $

  for every nonzero fractional $B$-ideal $I$. Thus the ideal norm is exactly
  divisor pushforward written multiplicatively.
]

#proof[
  Both sides are homomorphisms from $"FracId"(B)$ to the divisor group of
  $"Spec" A$, so it is enough to check a prime ideal $frak(q)|frak(p)$. By the
  prime-norm theorem,

  $ Phi_A ("N"_(B slash A) (frak(q)))=Phi_A (frak(p)^(f_(frak(q) slash frak(p)))) $

  $ =f_(frak(q) slash frak(p))[frak(p)]=pi_* Phi_B (frak(q)) $

  Multiplicativity proves the result for every fractional ideal. Explicitly,
  the coefficient of $[frak(p)]$ on either side is

  $ sum_(frak(q)|frak(p)) f_(frak(q) slash frak(p))v_(frak(q)) (I) $

  which recovers the valuation formula above.
]

#corollary(title: "Norm after Extending an Ideal")[
  For every nonzero fractional ideal $J$ of $A$,

  $ "N"_(B slash A) (J B)=J^n $
]

#proof[
  Under the ideal--divisor correspondence, extension of ideals is divisor
  pullback:

  $ Phi_B (J B)=pi^* Phi_A (J) $

  Applying the pushforward proposition gives

  $ Phi_A ("N"_(B slash A) (J B))=pi_* pi^* Phi_A (J) $

  For a prime divisor $[frak(p)]$, the fundamental identity from Chapter 3
  gives

  $ pi_* pi^* [frak(p)]=sum_(frak(q)|frak(p)) e_(frak(q) slash frak(p))f_(frak(q) slash frak(p))[frak(p)]=n[frak(p)] $

  Therefore the right-hand side is
  $n Phi_A (J)=Phi_A (J^n)$. Since $Phi_A$ is injective, the desired ideal
  identity follows.
]

#remark(title: "Pullback versus Pushforward")[
  The two divisor operations are determined on closed points by

  $ pi^* [frak(p)]=sum_(frak(q)|frak(p)) e_(frak(q) slash frak(p))[frak(q)] $

  $ pi_* [frak(q)]=f_(frak(q) slash frak(p))[frak(p)] $

  Thus ramification indices $e$ occur in pullback, whereas residue degrees $f$
  occur in pushforward. Their composite is multiplication by the generic
  degree:

  $ pi_* pi^* D=n D $

  Pushforward also preserves principal divisors in the precise form

  $ pi_* "div"_L (alpha)="div"_K ("N"_(L slash K) (alpha)) $

  This is the divisor version of the principal-ideal formula. Consequently,
  pushforward respects linear equivalence, and the ideal norm induces a map
  on class groups

  $ "Cl"(B)->"Cl"(A), quad [I] mapsto ["N"_(B slash A) (I)] $
]

#quote[
  Extending an ideal pulls a prime upward and counts ramification; taking its
  norm pushes primes downward and counts residue-field degree.
]

=== Absolute Norms in Number Fields

#definition(title: "Absolute Ideal Norm")[
  Let $K$ be a number field and let $0!=I subset.eq cal(O)_K$ be an integral
  ideal. Its #emph[absolute norm] is the positive integer

  $ "N"(I):=abs(cal(O)_K slash I) $
]

#proposition(title: "Basic Formulas for the Absolute Norm")[
  For nonzero integral ideals $I,J subset.eq cal(O)_K$,

  + The absolute norm is multiplicative:

    $ "N"(I J)="N"(I)"N"(J) $

  + If $0!=alpha in cal(O)_K$, then

    $ "N"(alpha cal(O)_K)=abs("N"_(K slash QQ) (alpha)) $

  + If $frak(q)$ lies above the rational prime $p$, then

    $ "N"(frak(q))=p^(f_(frak(q) slash (p))) $
]

#proof[
  The ideal norm $"N"_(cal(O)_K slash ZZ) (I)$ is an integral ideal of $ZZ$.
  By the quotient formula for module indices, its positive generator is the
  finite group index $abs(cal(O)_K slash I)$. The three formulas now follow
  from multiplicativity, compatibility with the field norm, and the
  prime-ideal formula.
]

#example(title: "Norms in the Gaussian Integers")[
    In $ZZ[i]$, the principal prime ideal $frak(q)=(2+i)$ lies above $5$.
    Since $"N"_(QQ(i) slash QQ) (2+i)=5$,

    $ "N"_(ZZ[i] slash ZZ) (frak(q))=(5), quad "N"(frak(q))=5 $

    On the other hand,

    $ (5)=(2+i)(2-i) $

    and therefore

    $ "N"((5))=25 $

    This is a useful distinction: a prime above $5$ has norm $5$, while the
  extended ideal $5ZZ[i]$ has norm $5^[QQ(i):QQ]=25$.
]

== The Dedekind--Kummer Theorem

The Dedekind--Kummer theorem turns factorization of a polynomial over a
residue field into factorization of a prime ideal in an integral closure. It
is one of the basic bridges between polynomial arithmetic and ideal
arithmetic.

#quote[
  #emph[Core idea.] Dedekind--Kummer transforms the ideal factorization of
  $frak(p)B$ into the factorization of a single polynomial over the residue
  field $kappa(frak(p))$. For number fields over $QQ$, this is precisely the
  passage from ideal factorization in a number ring to polynomial
  factorization over $FF_p$.
]

#theorem(title: "Primitive Element Theorem")[
  Every finite separable field extension is simple: if $L slash K$ is finite
  separable, then there exists $alpha in L$ such that

  $ L=K(alpha) $
]

In our setting, $B$ spans $L$ over $K$. After multiplying $alpha$ by a suitable
nonzero element of $A$, we may therefore choose an integral primitive element
$theta in B$ with $L=K(theta)$. Thus the primitive element theorem supplies a
single algebraic coordinate for $L slash K$; the remaining question is whether
the powers of this coordinate generate the whole integral closure $B$.

=== Power Bases and the Index Divisor

Fix such an integral primitive element $theta in B$, and let

$ f(T) in A[T] $

be its monic minimal polynomial. If $n=[L:K]$, then

$ A[theta]=A+A theta+dots+A theta^(n-1) $

is a free $A$-lattice in $L$, but it need not equal $B$.

#definition(title: "Monogenic Extensions and the Index Ideal")[
  The extension $B slash A$ is #emph[monogenic] if

  $ B=A[theta] $

  for some $theta in B$. In this case ${1,theta,dots,theta^(n-1)}$ is an
  integral power basis of $B$.

  For an integral primitive element $theta$, define its #emph[index ideal] by

  $ frak(i)_theta:=[B:A[theta]]_A $

  A nonzero prime $frak(p)$ of $A$ is #emph[good for $theta$] if
  $v_(frak(p)) (frak(i)_theta)=0$; equivalently, $frak(p)$ does not divide the
  index ideal.
]

#proposition(title: "The Index Divisor Measures Failure of Monogenicity")[
  For every nonzero prime $frak(p)$ of $A$,

  $ v_(frak(p)) (frak(i)_theta)="length"_(A_(frak(p))) (B_(frak(p)) slash A_(frak(p))[theta]) $

  Consequently, $frak(p)$ is good for $theta$ exactly when

  $ B_(frak(p))=A_(frak(p))[theta] $

  Under the ideal--divisor correspondence, the #emph[index divisor] is

  $ D_theta:=Phi_A (frak(i)_theta)=sum_frak(p) "length"_(A_(frak(p))) (B_(frak(p)) slash A_(frak(p))[theta])[frak(p)] $

  It is supported at the finitely many primes where the power basis generated
  by $theta$ fails to be an integral basis locally.
]

#proof[
  Apply the geometric module-index formula to the inclusion
  $A[theta] subset.eq B$. The coefficient at $frak(p)$ is the length of the
  localized quotient. A finite-length module over the local ring
  $A_(frak(p))$ has length zero exactly when it is zero, which gives the local
  equality criterion. Finiteness of the support follows because
  $frak(i)_theta$ is a nonzero integral ideal.
]

#remark(title: "Why an Index Condition Appears")[
  The polynomial $f$ always describes the order $A[theta]$. It describes the
  maximal order $B$ at $frak(p)$ only when $frak(p)$ is absent from the index
  divisor. Dedekind--Kummer is therefore a local monogenicity theorem: one
  generator need not work everywhere, but it works at every prime outside a
  finite obstruction divisor.
]

=== Statement and Proof

#theorem(title: [Dedekind--Kummer])[
  Let $theta in B$ satisfy $L=K(theta)$, let $f in A[T]$ be its monic minimal
  polynomial, and let $frak(p)$ be a nonzero prime of $A$ that is good for
  $theta$. Factor the reduction of $f$ into distinct monic irreducibles over the
  residue field $kappa(frak(p))=A slash frak(p)$:

  $ overline(f)=product_(i=1)^r overline(g)_i^(e_i) $

  Choose any monic lift $g_i in A[T]$ of each $overline(g)_i$, and put

  $ frak(q)_i:=frak(p)B+g_i (theta)B=(frak(p),g_i (theta)) $

  Then the $frak(q)_i$ are precisely the distinct prime ideals of $B$ above
  $frak(p)$, and

  $ frak(p)B=product_(i=1)^r frak(q)_i^(e_i) $

  Moreover,

  $ f_(frak(q)_i slash frak(p))=deg(overline(g)_i) $

  In particular, if $B=A[theta]$, the conclusion holds for every nonzero prime
  $frak(p)$ of $A$.
]

#proof[
  Since $frak(p)$ is good for $theta$, the index-divisor criterion gives

  $ B_(frak(p))=A_(frak(p))[theta] $

  Localizing does not change the fiber over $frak(p)$, because every element
  of $A$ outside $frak(p)$ becomes a unit modulo $frak(p)$. Therefore

  $ B slash frak(p)B tilde.eq B_(frak(p)) slash frak(p)B_(frak(p)) $

  $ tilde.eq kappa(frak(p))[T] slash (overline(f)) $

  The Chinese remainder theorem now gives the scheme-theoretic decomposition

  $ B slash frak(p)B tilde.eq product_(i=1)^r kappa(frak(p))[T] slash (overline(g)_i^(e_i)) $

  The maximal ideals of the right-hand side are indexed by the distinct
  polynomials $overline(g)_i$. Their inverse images in $B$ are exactly
  $frak(q)_i=(frak(p),g_i (theta))$, so these are all the primes above
  $frak(p)$. Furthermore,

  $ B slash frak(q)_i tilde.eq kappa(frak(p))[T] slash (overline(g)_i) $

  is a field of degree $deg(overline(g)_i)$ over $kappa(frak(p))$. This proves
  the residue-degree formula.

  It remains to identify the ramification exponents. Localize the fiber at
  the point $frak(q)_i$. All the factors $overline(g)_j$ with $j!=i$ become
  units, and hence

  $ B_(frak(q)_i) slash frak(p)B_(frak(q)_i) tilde.eq (kappa(frak(p))[T] slash (overline(g)_i^(e_i)))_((overline(g)_i)) $

  The maximal ideal on the right has nilpotence order $e_i$. On the left,
  $B_(frak(q)_i)$ is a DVR and

  $ frak(p)B_(frak(q)_i)=(frak(q)_i B_(frak(q)_i))^(e_(frak(q)_i slash frak(p))) $

  so the maximal ideal has nilpotence order
  $e_(frak(q)_i slash frak(p))$. These orders are equal, proving
  $e_(frak(q)_i slash frak(p))=e_i$ and hence the asserted prime-ideal
  factorization.
]

The theorem can be remembered through the following dictionary.

#block(breakable: false)[
  #align(center, table(
    columns: (1fr, 1fr),
    align: (center, center),
    inset: (x: 12pt, y: 5.5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[$overline(f)$ modulo $frak(p)$]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[$frak(p)B$ in $B$]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    [irreducible factor $overline(g)_i$],
    [prime ideal $frak(q)_i=(frak(p),g_i (theta))$],
    [$deg(overline(g)_i)$],
    [residue degree $f_(frak(q)_i slash frak(p))$],
    [multiplicity $e_i$],
    [ramification index $e_(frak(q)_i slash frak(p))$],
  ))
]

#remark(title: "The Fiber and Divisor Pictures")[
  Dedekind--Kummer can be read directly from the fiber

  $ "Spec"(B slash frak(p)B) tilde.eq ⊔_(i=1)^r "Spec"(kappa(frak(p))[T] slash (overline(g)_i^(e_i))) $

  Each irreducible factor $overline(g)_i$ gives one closed point of residue
  degree $deg(overline(g)_i)$, while its exponent $e_i$ gives the
  scheme-theoretic thickness of that point. In divisor language,

  $ pi^* [frak(p)]=sum_(i=1)^r e_i [frak(q)_i], quad pi_* [frak(q)_i]=deg(overline(g)_i)[frak(p)] $

  Thus the factorization of $overline(f)$ simultaneously displays the
  pullback and pushforward data of the closed point $[frak(p)]$.
]

=== Simple Applications

#corollary(title: "Splitting in Quadratic Fields")[
  Let $d!=1$ be squarefree, let $K=QQ(sqrt(d))$, and define

  $ omega=cases(
    (1+sqrt(d))\/2 & quad d equiv 1 mod 4,
    sqrt(d) & quad d equiv.not 1 mod 4
  ) $

  By Chapter 3, $cal(O)_K=ZZ[omega]$. The minimal polynomial of $omega$ is

  $ F(T)=cases(
    T^2-T+(1-d)\/4 & quad d equiv 1 mod 4,
    T^2-d & quad d equiv.not 1 mod 4
  ) $

  For every rational prime $p$, the factorization of $F$ modulo $p$
  determines the factorization of $(p)$ in $cal(O)_K$:

  + If $overline(F)$ is irreducible, then $(p)$ is inert.

  + If $overline(F)$ is a product of two distinct linear factors, then $(p)$
    splits into two distinct primes.

  + If $overline(F)$ is the square of a linear factor, then $(p)$ is ramified.
]

#proof[
  The ring of integers is monogenic with generator $omega$, so there is no
  index obstruction. The three cases are exactly the three possible
  factorizations of a monic quadratic polynomial over $FF_p$, and
  Dedekind--Kummer translates their degrees and multiplicities into residue
  degrees and ramification indices.
]

#remark(title: "The Discriminant Test in Degree Two")[
  The polynomial discriminant of $F$ is

  $ Delta_K=cases(
    d & quad d equiv 1 mod 4,
    4d & quad d equiv.not 1 mod 4
  ) $

  A quadratic polynomial has a repeated factor modulo $p$ exactly when its
  discriminant vanishes modulo $p$. Hence

  $ p " ramifies in " K <=> p divides Delta_K $

  For odd $p$ not dividing $Delta_K$, the prime splits or remains inert
  according as $Delta_K$ is or is not a square modulo $p$.
]

#example(title: [Running the Algorithm in $ZZ[i]$])[
  Here $theta=i$, $B=ZZ[i]$, and $f(T)=T^2+1$.

  + Modulo $2$,

    $ overline(f)=(T+1)^2 $

    Thus $(2)=(2,i+1)^2=(1+i)^2$ is totally ramified.

  + Modulo $3$, the polynomial $T^2+1$ is irreducible. Thus $(3)$ is inert
    and has residue degree $2$.

  + Modulo $5$,

    $ overline(f)=(T-2)(T+2) $

    Hence

    $ (5)=(5,i-2)(5,i+2) $

    and $(5)$ splits completely.
]

#example(title: [Three Behaviors in $QQ(zeta_5)$])[
  Let $zeta_5$ be a primitive fifth root of unity. Using the standard fact
  $cal(O)_(QQ(zeta_5))=ZZ[zeta_5]$, Dedekind--Kummer applies to

  $ f(T)=T^4+T^3+T^2+T+1 $

  + The reduction of $f$ modulo $2$ is irreducible, so $(2)$ is inert with
    residue degree $4$.

  + Modulo $5$,

    $ overline(f)=(T-1)^4 $

    so

    $ (5)=(5,zeta_5-1)^4 $

    is totally ramified.

  + Modulo $11$,

    $ overline(f)=(T-4)(T-9)(T-5)(T-3) $

    so $(11)$ splits completely into four distinct primes of residue degree
    $1$.
]

#example(title: "Why the Index Condition Cannot Be Dropped")[
  Let $K=QQ(sqrt(5))$ and choose the integral primitive element
  $theta=sqrt(5)$. The maximal order is

  $ B=ZZ[(1+sqrt(5))\/2] $

  and the power order $ZZ[theta]$ has index ideal

  $ [B:ZZ[theta]]_ZZ=(2) $

  Indeed, if $omega=(1+sqrt(5))\/2$, then $theta=2omega-1$, so the two power
  bases differ by a matrix of determinant $2$.

  The polynomial $T^2-5$ reduces modulo $2$ to $(T-1)^2$. Applying the theorem
  without checking the index would incorrectly suggest ramification. But the
  integral generator $omega$ has minimal polynomial

  $ T^2-T-1 $

  whose reduction $T^2+T+1$ is irreducible over $FF_2$. Therefore $(2)$ is
  actually inert in $QQ(sqrt(5))$. The failure occurs exactly at the prime
  supporting the index divisor.
]

== The Conductor

Dedekind--Kummer compares the power order $A[theta]$ with the integral closure
$B$. The index ideal measures the size of their difference as $A$-lattices.
The #emph[conductor] records a complementary piece of information: it is the
largest ideal of the maximal order $B$ that is already contained in the
smaller order.

#definition(title: "Orders and the Conductor")[
  An #emph[$A$-order] in $L$ is an $A$-subalgebra $C subset.eq L$ that is an
  $A$-lattice in $L$. Its integral closure is $B$. The #emph[conductor of $C$
  in $B$] is the colon ideal

  $ frak(f)_(B slash C):=(C:B):={x in L | x B subset.eq C} $
]

#proposition(title: "Equivalent Descriptions of the Conductor")[
  Let $C subset.eq B$ be an $A$-order. Then

  $ frak(f)_(B slash C)="Ann"_C (B slash C) $

  Moreover, $frak(f)_(B slash C)$ is a nonzero ideal of both $C$ and $B$, and
  it is the largest $B$-ideal contained in $C$.
]

#proof[
  Since $1 in B$, every $x$ satisfying $x B subset.eq C$ already lies in $C$.
  Such an $x$ annihilates $B slash C$, and the converse is immediate; this
  proves the displayed equality.

  If $x in frak(f)_(B slash C)$ and $b in B$, then

  $ (b x) B subset.eq x B subset.eq C $

  so $b x$ again belongs to the conductor. Thus it is a $B$-ideal, and hence
  also a $C$-ideal. The lattices $B$ and $C$ are commensurable, so some
  $0!=a in A$ satisfies $a B subset.eq C$; therefore the conductor is nonzero.
  Finally, every $B$-ideal $J subset.eq C$ satisfies $J B subset.eq C$, hence
  $J subset.eq frak(f)_(B slash C)$.
]

#quote[
  #emph[Core idea.] The index measures how large $B slash C$ is, while the
  conductor measures how much of $B$ can be multiplied back into $C$. One is
  a determinant; the other is an annihilator.
]

#proposition(title: "The Conductor Locus and the Index Divisor")[
  For every nonzero prime $frak(p)$ of $A$, the following are equivalent.

  + $C_(frak(p))=B_(frak(p))$.

  + $frak(f)_(B slash C) B_(frak(p))=B_(frak(p))$.

  + There is an $s in frak(f)_(B slash C) inter A$ with
    $s in.not frak(p)$.

  + $v_(frak(p)) ([B:C]_A)=0$.

  Consequently,

  $ sqrt([B:C]_A)=sqrt(frak(f)_(B slash C) inter A) $

  Thus the index ideal and the conductor have the same bad primes, although
  their multiplicities need not agree.
]

#proof[
  Localization commutes with the colon ideal because $B$ is finite over $A$:

  $ frak(f)_(B slash C) B_(frak(p))=(C_(frak(p)):B_(frak(p))) $

  The right-hand side contains $1$ exactly when
  $C_(frak(p))=B_(frak(p))$. The localized conductor is the unit ideal exactly
  when it contains an element of $A$ outside $frak(p)$, which gives the third
  condition. Finally, the module-index formula gives

  $ v_(frak(p)) ([B:C]_A)="length"_(A_(frak(p))) (B_(frak(p)) slash C_(frak(p))) $

  so its valuation vanishes exactly when the two localized orders coincide.
  The equivalent conditions show that the two ideals have the same prime
  divisors, proving the radical identity. Equivalently, one may use

  $ [B:C]_A="Fitt"_0^A (B slash C) subset.eq "Ann"_A (B slash C)=frak(f)_(B slash C) inter A $

  together with the fact that the zeroth Fitting ideal and the annihilator of
  a finite torsion module have the same support.
]

#pagebreak(weak: true)

#remark(title: "The Geometry of an Order")[
  Put $S:="Spec" A$, $X_C:="Spec" C$, and $X_B:="Spec" B$. Because an
  $A$-order is a finite projective $A$-module of rank $n=[L:K]$, the map

  $ pi_C:X_C->S $

  is finite and flat of degree $n$. Its generic fiber is

  $ X_C times_S "Spec" K tilde.eq "Spec" L tilde.eq X_B times_S "Spec" K $

  Thus an order is a one-dimensional arithmetic model of the field $L$: all
  orders have the same generic fiber, but they may have different closed
  fibers. Since $B slash C$ is torsion over $A$, these models differ at only
  finitely many closed points.

  The finite birational map

  $ nu:X_B->X_C $

  is the normalization of $X_C$. The scheme $X_B$ is regular, whereas $X_C$
  may have nonnormal curve singularities. Geometrically, normalization repairs
  those singular points and may separate several branches lying over one
  closed point of $X_C$.
]

#remark(title: "The Conductor Square")[
  Write $frak(f)=frak(f)_(B slash C)$ and put

  $ Z_B:="Spec"(B slash frak(f)), quad Z_C:="Spec"(C slash frak(f)) $

  Since $frak(f)$ is an ideal in both rings, it defines finite closed
  subschemes $Z_B subset.eq X_B$ and $Z_C subset.eq X_C$. They fit into the
  #emph[conductor square]

  #align(center, diagram(
    spacing: (22mm, 9mm),
    node-inset: 2pt,
    node((0, 0), [$Z_B="Spec"(B slash frak(f))$]),
    node((1, 0), [$X_B="Spec" B$]),
    node((0, 1), [$Z_C="Spec"(C slash frak(f))$]),
    node((1, 1), [$X_C="Spec" C$]),
    edge((0, 0), (1, 0), "->"),
    edge((0, 0), (0, 1), "->"),
    edge((1, 0), (1, 1), "->", label: [$nu$]),
    edge((0, 1), (1, 1), "->"),
  ))

  Algebraically, the square is encoded by the pullback identity

  $ C tilde.eq B times_(B slash frak(f)) (C slash frak(f)) $

  Geometrically, $X_C$ is reconstructed from its normalization $X_B$ by
  replacing the finite subscheme $Z_B$ with $Z_C$. This operation is called
  #emph[pinching]. Outside $Z_C$, normalization is already an isomorphism, so
  the conductor is the scheme-theoretic interface along which the singular
  model is glued back together.
]

#remark(title: "The Conductor Divisor")[
  Since $B$ is Dedekind, the conductor has a unique prime-ideal factorization

  $ frak(f)=product_frak(q) frak(q)^(c_frak(q)) $

  and therefore determines the effective #emph[conductor divisor]

  $ D_"cond" (B slash C):=sum_frak(q) c_frak(q)[frak(q)] $

  Locally at $frak(q)$,

  $ frak(f) B_(frak(q))=(frak(q)B_(frak(q)))^(c_frak(q)) $

  so $c_frak(q)$ measures the thickness of the correction locus along
  $[frak(q)]$. Its support maps precisely onto the support of the index divisor
  $Phi_A ([B:C]_A)$ in $"Spec" A$.
]

#remark(title: [Connection with Dedekind--Kummer])[
  For $C=A[theta]$, a prime $frak(p)$ is good for $theta$ exactly when it lies
  outside the conductor locus. Hence Dedekind--Kummer reads the factorization
  of $frak(p)B$ from $overline(f)$ exactly where the normalization
  $"Spec" B->"Spec" C$ is locally an isomorphism. The index condition and the
  conductor condition describe the same exceptional set.
]

#example(title: "Quadratic Orders")[

Let $K$ be a quadratic number field, write $B=cal(O)_K=ZZ[omega]$, and let
$m>=1$. The subring

$ C_m:=ZZ+m B=ZZ[m omega] $

is an order of index $m$. Its conductor is

$ frak(f)_(B slash C_m)=m B $

Indeed, write $omega^2=t omega-u$ with $t,u in ZZ$. For $x=a+b omega in B$,
the conditions $x,x omega in C_m$ imply $m divides b$ and
$m divides a+b t$, hence $m divides a$. Thus $x in m B$; the reverse inclusion
is immediate. Moreover,

$ [B:C_m]_ZZ=(m), quad frak(f)_(B slash C_m) inter ZZ=(m), quad "disc"(C_m)=m^2 "disc"(B) $

For $K=QQ(sqrt(5))$ and $C=ZZ[sqrt(5)]$, one has $m=2$ and
$frak(f)_(B slash C)=2 B$, explaining again why the prime $2$ is exactly the
exceptional prime for the generator $sqrt(5)$.
]
