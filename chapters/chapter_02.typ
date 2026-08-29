#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Étale Algebras

The chapter begins with separability for field extensions, packages that
notion geometrically as étaleness, and then develops trace and norm as the
additive and multiplicative operations along finite maps. Each layer motivates
the next while keeping the field-theoretic, geometric, and arithmetic
viewpoints visible.

== Separability

Separability says that the algebraic conjugates of an element remain distinct.
It is the condition that allows a finite field extension to behave, after
passing to an algebraic closure, like a finite collection of distinct points.
We begin with a review of the field-theoretic definitions and their most useful
consequences.

=== Basic Definitions

#definition(title: "Separable Polynomials, Elements, and Extensions")[
  Let $K$ be a field and fix an algebraic closure $overline(K)$.

  + A nonconstant polynomial $f in K[X]$ is #emph[separable over $K$] if its
    roots in $overline(K)$ are distinct.

  + An algebraic element $alpha in overline(K)$ is #emph[separable over $K$]
    if its minimal polynomial $m_(alpha,K) in K[X]$ is separable.

  + An algebraic extension $L slash K$ is #emph[separable] if every element of
    $L$ is separable over $K$.

  For a general, not necessarily algebraic extension, separability means that
  every element of $L$ that is algebraic over $K$ is separable over $K$.
]

#remark(title: "Separable Does Not Mean Split")[
  A polynomial may be separable without having any root in its ground field.
  For example, $X^2-2$ is separable over $QQ$ but does not split over $QQ$.
  Separability asks whether the roots are #emph[distinct] in an algebraic
  closure, whereas splitting asks whether they already lie in the chosen
  field.
]

#proposition(title: "The Derivative Criterion")[
  Let $f in K[X]$ be nonconstant and let $f'$ be its formal derivative. The
  following conditions are equivalent.

  + The polynomial $f$ is separable.

  + The polynomials $f$ and $f'$ have no common root in $overline(K)$.

  + We have

    $ "gcd"(f,f')=1 $

  If $f$ is irreducible, these are also equivalent to $f'!=0$.
]

#proof[
  Over $overline(K)$, write

  $ f(X)=c product_(i=1)^r (X-alpha_i)^(e_i) $

  with distinct $alpha_i$. The factor $X-alpha_i$ divides both $f$ and $f'$ if
  and only if $e_i>=2$. Thus $f$ has no repeated root precisely when
  $"gcd"(f,f')=1$. If $f$ is irreducible, its greatest common divisor with
  $f'$ is either $1$ or $f$; the second possibility occurs exactly when
  $f'=0$.
]

#corollary(title: "The Role of the Characteristic")[
  If $"char"(K)=0$, every irreducible polynomial over $K$ is separable. If
  $"char"(K)=p>0$, then

  $ f'=0 <=> f(X)=g(X^p) $

  for some $g in K[X]$. Hence inseparability can occur only in positive
  characteristic.
]

#proof[
  In characteristic zero, a nonconstant polynomial has nonzero derivative. In
  characteristic $p$, the derivative of $X^n$ vanishes exactly when $p$ divides
  $n$. Therefore $f'=0$ precisely when every exponent occurring in $f$ is
  divisible by $p$.
]

=== Perfect Fields

#definition(title: "Perfect Field")[
  A field $K$ is #emph[perfect] if every algebraic extension of $K$ is
  separable. Equivalently, every irreducible polynomial in $K[X]$ is
  separable.
]

#theorem(title: "Characterization of Perfect Fields")[
  A field $K$ is perfect if and only if either

  + $"char"(K)=0$; or

  + $"char"(K)=p>0$ and the Frobenius map

    $ "Frob"_K:K->K, quad a mapsto a^p $

    is surjective.

  In particular, every field of characteristic zero and every finite field is
  perfect.
]

#proof[
  The characteristic-zero statement follows from the derivative criterion.
  Suppose $"char"(K)=p$ and Frobenius is surjective. If an irreducible
  polynomial $f$ had $f'=0$, then

  $ f(X)=sum_i a_i X^(p i)=(sum_i b_i X^i)^p $

  after choosing $b_i in K$ with $b_i^p=a_i$. This contradicts irreducibility
  unless $f$ is linear. Conversely, if Frobenius is not surjective, choose
  $a in K$ that is not a $p$-th power. Then $X^p-a$ is irreducible and has
  derivative zero, so $K$ is not perfect. Finally, Frobenius is injective on
  every field and is therefore bijective when the field is finite.
]

#example(title: "A Basic Inseparable Extension")[
  Let $K=FF_p (t)$ and let

  $ L=K(u), quad u^p=t $

  The element $t$ is not a $p$-th power in $K$, so $X^p-t$ is irreducible.
  However,

  $ X^p-t=(X-u)^p $

  over $overline(K)$. Thus $L slash K$ has degree $p$ but is not separable. It
  is a #emph[purely inseparable] extension: every element of $L$ has some
  $p$-power lying in $K$.
]

=== Separable Degree

#definition(title: "Separable and Inseparable Degrees")[
  Let $L slash K$ be a finite extension and fix an algebraic closure
  $overline(K)$. Its #emph[separable degree] is

  $ [L:K]_"s":=abs("Hom"_K (L,overline(K))) $

  and its #emph[inseparable degree] is

  $ [L:K]_"i":=[L:K] slash [L:K]_"s" $

  Thus

  $ [L:K]=[L:K]_"s" dot [L:K]_"i" $
]

#proposition(title: "Basic Properties of the Separable Degree")[
  Let $L_"s"$ be the set of elements of $L$ that are separable over $K$.
  Then $L_"s"$ is the largest intermediate field separable over $K$, the
  extension $L slash L_"s"$ is purely inseparable, and

  $ [L:K]_"s"=[L_"s":K], quad [L:K]_"i"=[L:L_"s"] $

  Consequently,

  + $L slash K$ is separable exactly when $[L:K]_"s"=[L:K]$;

  + $L slash K$ is purely inseparable exactly when $[L:K]_"s"=1$;

  + in characteristic $p>0$, the inseparable degree is a power of $p$;

  + for every finite tower $K subset.eq E subset.eq L$, both degrees are
    multiplicative:

    $ [L:K]_"s"=[L:E]_"s" dot [E:K]_"s", quad [L:K]_"i"=[L:E]_"i" dot [E:K]_"i" $
]

#remark(title: "Distinct Geometric Points versus Their Lengths")[
  The algebra $L ⊗_K overline(K)$ has exactly $[L:K]_"s"$ geometric
  points, and every point has scheme-theoretic length $[L:K]_"i"$. Thus the
  ordinary degree counts points with multiplicity:

  $ [L:K]=underbrace([L:K]_"s")_("distinct points") dot underbrace([L:K]_"i")_("length of each point") $
]

=== Finite Separable Extensions

#theorem(title: "Primitive Element Theorem")[
  Every finite separable extension is simple: if $L slash K$ is finite
  separable, then $L=K(alpha)$ for some $alpha in L$.
]

#theorem(title: "Equivalent Forms of Separability")[
  Let $L slash K$ be a finite extension of degree $n$, and let $overline(K)$ be
  an algebraic closure of $K$. The following conditions are equivalent.

  + The extension $L slash K$ is separable.

  + There are exactly $n$ distinct $K$-embeddings

    $ sigma:L->overline(K) $

  + After extending scalars to $overline(K)$, there is an isomorphism of
    $overline(K)$-algebras

    $ L ⊗_K overline(K) tilde.eq product_(sigma:L->overline(K)) overline(K) tilde.eq overline(K)^n $
]

#proof[
  Suppose first that $L slash K$ is separable. By the primitive element
  theorem, $L=K(alpha)$ for some $alpha$, and the minimal polynomial
  $m_(alpha,K)$ has $n$ distinct roots $alpha_1,dots,alpha_n$ in
  $overline(K)$. Each embedding is determined by the image of $alpha$, which
  may be any one of these roots. Hence there are exactly $n$ embeddings.

  Moreover,

  $ L ⊗_K overline(K) tilde.eq overline(K)[X] slash (m_(alpha,K)) $

  Since the linear factors $X-alpha_i$ are pairwise coprime, the Chinese
  remainder theorem gives

  $ overline(K)[X] slash (m_(alpha,K)) tilde.eq product_(i=1)^n overline(K)[X] slash (X-alpha_i) tilde.eq overline(K)^n $

  Conversely, the number of $K$-embeddings of any finite extension into
  $overline(K)$ is at most its degree, with equality exactly when all minimal
  polynomials involved have distinct roots. If $L slash K$ is not separable,
  this number is strictly less than $n$, and the scalar extension acquires
  nilpotents. This proves all equivalences.
]

#pagebreak(weak: true)

#remark(title: "The Geometric Base-Change Criterion")[
  Put $X="Spec" K$ and $Y="Spec" L$. For every field extension $K' slash K$,
  base change gives

  $ Y_(K')=Y times_X "Spec"(K')="Spec"(L ⊗_K K') $

  #quote[
    Separability is reducedness that survives arbitrary base change.
  ]

  The extension $L slash K$ is separable if and only if $Y$ is
  #emph[geometrically reduced] over $K$. Concretely, the following conditions
  are equivalent:

  + $L slash K$ is separable;

  + $L ⊗_K K'$ is reduced for every field extension $K' slash K$;

  + $L ⊗_K overline(K)$ is reduced;

  + after base change to $overline(K)$, the scheme $Y$ becomes a disjoint union
    of $n=[L:K]$ geometric points:

    $ Y_(overline(K)) tilde.eq ⊔_(sigma:L->overline(K)) "Spec"(overline(K)) $

  Indeed, a separable minimal polynomial becomes a product of distinct linear
  factors over $overline(K)$, so its coordinate algebra becomes
  $overline(K)^n$. A repeated root instead produces a nonzero nilpotent, and
  the geometric fiber is nonreduced. Thus separability is exactly the
  assertion that distinct points remain distinct after arbitrary base change.

  If $K^"sep"$ denotes a separable closure, there is also the splitting
  criterion

  $ L slash K " is separable" <=> L ⊗_K K^"sep" tilde.eq (K^"sep")^n $

  One should not weaken this to saying merely that $L ⊗_K K^"sep"$ is reduced.
  For example, a purely inseparable extension can remain a field after base
  change to $K^"sep"$. Passing to an algebraic closure, or requiring
  reducedness after #emph[every] field extension, is what detects
  inseparability.
]

=== Stability Properties

#proposition(title: "Separability in Towers and under Base Change")[
  Let $K subset.eq E subset.eq L$ be algebraic field extensions.

  + If $L slash K$ is separable, then both $E slash K$ and $L slash E$ are
    separable.

  + If $E slash K$ and $L slash E$ are separable, then $L slash K$ is
    separable.

  + The compositum of two separable extensions of $K$ is separable over $K$.

  + If $L slash K$ is finite separable and $K' slash K$ is any field
    extension, then

    $ L ⊗_K K' tilde.eq product_(i=1)^r L_i $

    for finite separable field extensions $L_i slash K'$. Thus separability is
    preserved by arbitrary extension of the ground field.
]

#proof[
  For the first assertion, elements of $E$ are already separable over $K$, and
  the minimal polynomial over $E$ of an element of $L$ divides its separable
  minimal polynomial over $K$. Transitivity follows by counting embeddings in
  the two stages of the tower. If $L_1 slash K$ and $L_2 slash K$ are
  separable, then $L_1 L_2 slash L_1$ is separable because minimal polynomials
  over $L_1$ divide the corresponding separable polynomials over $K$.
  Transitivity now shows that $L_1 L_2 slash K$ is separable.

  For base change, write a finite separable extension as $L=K(alpha)$. The
  polynomial $m_(alpha,K)$ remains square-free over $K'$ and factors there as a
  product of distinct irreducible polynomials $f_1 dots f_r$. Consequently,

  $ L ⊗_K K' tilde.eq K'[X] slash (m_(alpha,K)) tilde.eq product_(i=1)^r K'[X] slash (f_i) $

  and each factor is a finite separable extension of $K'$.
]

#remark(title: "Why Separability Matters")[
  Separability connects field theory, arithmetic, and geometry.

  + #emph[Distinct conjugates.] A degree-$n$ separable extension has the
    expected $n$ embeddings into an algebraic closure. These embeddings make
    trace and norm computable as sums and products of conjugates.

  + #emph[Nondegenerate arithmetic.] The trace pairing and discriminant detect
    linear independence and control integral bases, ramification, and the
    geometry of numbers. Number fields are automatically separable because
    they have characteristic zero.

  + #emph[Reduced geometric fibers.] A finite separable field extension becomes
    a product of copies of an algebraic closure after base change. There are no
    nilpotent directions, so the corresponding geometric points are distinct.

  + #emph[Galois theory.] A finite extension is Galois precisely when it is
    both normal and separable. Separability supplies the full set of distinct
    embeddings; normality ensures that their images remain inside the field.

  + #emph[Étale algebras.] Finite étale algebras over a field are exactly finite
    products of finite separable field extensions. Thus separability is the
    field-theoretic model for the word #emph[étale].
]

#example(title: "Number Fields and Finite Fields")[
  If $K$ is a number field of degree $n$ over $QQ$, then $K slash QQ$ is
  separable and has exactly $n$ embeddings into $CC$. If $r_1$ of them are real
  and $2r_2$ are nonreal, paired by complex conjugation, then

  $ n=r_1+2r_2 $

  This is the starting point of the Minkowski embedding.

  Likewise, every extension $FF_(q^n) slash FF_q$ is separable. Its embeddings
  into an algebraic closure are generated by Frobenius:

  $ x mapsto x^q $
]

#example(title: "What Inseparability Looks Like Geometrically")[
  Return to $K=FF_p (t)$ and $L=K(u)$ with $u^p=t$. There is only one
  $K$-embedding $L->overline(K)$, although $[L:K]=p$. After base change,

  $ L ⊗_K overline(K) tilde.eq overline(K)[X] slash ((X-u)^p) tilde.eq overline(K)[epsilon] slash (epsilon^p) $

  The class of $epsilon$ is a nonzero nilpotent. Thus the single geometric
  point occurs with multiplicity $p$ instead of splitting into $p$ distinct
  points. This is exactly the behavior that separability, and later étaleness,
  rules out.
]

== Étale Algebras and Étale Morphisms

The word #emph[étale] means that a map has no ramification and no infinitesimal
thickening. It is the algebro-geometric analogue of a local diffeomorphism, or
of a covering map when the morphism is finite. In short, étale morphisms are
flat families of discrete reduced points.

=== Étale Algebras over a Field

#definition(title: "Finite Étale Algebra over a Field")[
  Let $K$ be a field. A #emph[finite étale $K$-algebra] is a finite-dimensional
  commutative $K$-algebra of the form

  $ B=L_1 times dots times L_r $

  where each $L_i slash K$ is a finite separable field extension. Its degree is
  $deg_K (B)=dim_K (B)$. In particular, a field $L$ is a finite étale
  $K$-algebra precisely when $L slash K$ is finite separable.
]

#theorem(title: "Characterizations over a Field")[
  Let $B$ be a finite-dimensional commutative $K$-algebra, and put
  $n=dim_K (B)$. The following conditions are equivalent.

  + The algebra $B$ is finite étale over $K$.

  + The algebra $B$ is #emph[geometrically reduced]: for every field extension
    $K' slash K$, the algebra $B ⊗_K K'$ is reduced.

  + The algebra obtained over an algebraic closure splits as

    $ B ⊗_K overline(K) tilde.eq overline(K)^n $

  + The module of Kähler differentials vanishes:

    $ Omega_(B slash K)=0 $
]

#proof[
  A finite-dimensional commutative $K$-algebra is Artinian. If it is reduced,
  it is a finite product of fields. Geometric reducedness therefore gives

  $ B=L_1 times dots times L_r $

  and each $L_i slash K$ is separable by the geometric base-change criterion.
  Conversely, a product of finite separable extensions becomes
  $overline(K)^n$ over $overline(K)$ and remains reduced after every base
  change.

  For a finite field extension $L slash K$, the equality
  $Omega_(L slash K)=0$ is equivalent to separability; this can be checked from
  a presentation $L=K[alpha]$, since

  $ Omega_(L slash K) tilde.eq L "d"alpha slash (m_(alpha,K)' (alpha) "d"alpha) $

  Products give the assertion for $B$.
]

#example(title: "A Polynomial Algebra")[
  For a monic polynomial $f in K[X]$, the algebra

  $ B=K[X] slash (f) $

  is finite étale over $K$ if and only if $f$ is separable, equivalently

  $ "gcd"(f,f')=1 $

  In contrast, the dual numbers $K[epsilon] slash (epsilon^2)$ are not étale:
  they contain a nonzero nilpotent and have $Omega_(B slash K)!=0$.
]

#proposition(title: "Finite Étale Algebras as Galois Sets")[
  Let

  $ G_K="Gal"(K^"sep" slash K) $

  be the absolute Galois group. The contravariant functor

  $ B mapsto Hom_(Alg_K) (B,K^"sep") $

  gives an anti-equivalence between finite étale $K$-algebras and finite sets
  with a continuous action of $G_K$. Under this correspondence, field
  extensions correspond to transitive $G_K$-sets.
]

#remark[
  This is the first appearance of a central principle: finite étale geometry
  over a field is another language for finite Galois actions. Passing from an
  algebra to its spectrum reverses arrows, which explains the
  anti-equivalence.
]

=== Étale Morphisms of Schemes

#definition(title: "Étale Morphism")[
  A morphism of schemes $f:X->Y$ is #emph[étale] if it is locally of finite
  presentation, flat, and unramified. For a morphism locally of finite
  presentation, the unramified condition is equivalent to

  $ Omega_(X slash Y)=0 $

  where $Omega_(X slash Y)$ is the sheaf of relative Kähler differentials.
]

Flatness says that the fibers vary without algebraic jumps, while
$Omega_(X slash Y)=0$ says that there are no nonzero tangent directions along
the fibers. Together they describe a family of discrete reduced points.

#theorem(title: "Equivalent Characterizations of Étale Morphisms")[
  For a morphism $f:X->Y$, the following conditions are equivalent.

  + The morphism $f$ is étale.

  + The morphism $f$ is smooth of relative dimension zero.

  + The morphism $f$ is locally of finite presentation and formally étale:
    maps into $X$ lift uniquely across nilpotent thickenings over $Y$.

  + Locally on $X$ and $Y$, the morphism has a standard étale presentation

    $ B=(A[T_1,dots,T_r] slash (F_1,dots,F_r))_g $

    for which the Jacobian determinant

    $ det(((∂ F_i)/(∂ T_j))_(1<=i,j<=r)) $

    is a unit in $B$.

  + The morphism is flat and locally of finite presentation, and every
    geometric fiber is a zero-dimensional reduced scheme.
]

#proposition(title: "Stability and Locality")[
  Étale morphisms satisfy the following fundamental properties.

  + A composition of étale morphisms is étale.

  + Étaleness is preserved by arbitrary base change. If $X->Y$ is étale and
    $Y'->Y$ is any morphism, then

    $ X times_Y Y'->Y' $

    is étale.

  + Open immersions are étale, and every étale morphism is an open map.

  + Finite étale morphisms remain finite étale after arbitrary base change.
]

#proofsketch[
  Local finite presentation and flatness are preserved by composition and base
  change. Relative differentials satisfy the corresponding base-change and
  transitivity formulas, so their vanishing is preserved as well. The openness
  statement follows from the general theorem that a flat morphism locally of
  finite presentation is open.
]

#remark(title: "The Infinitesimal Lifting Property")[
  On affine schemes, formal étaleness says that for every $A$-algebra $C$ and
  every nilpotent ideal $N subset.eq C$, reduction induces a bijection

  $ Hom_(Alg_A) (B,C) -> Hom_(Alg_A) (B,C slash N) $

  Existence means that infinitesimal deformations lift; uniqueness means that
  there are no relative tangent directions. An open immersion is étale, which
  also shows that an étale morphism need not be finite.
]

#remark(title: "Why Flatness Is Necessary")[
  Vanishing differentials alone do not imply étaleness. For example,

  $ Omega_(FF_p slash ZZ)=0 $

  but $ZZ->FF_p$ is not flat. Geometrically, the closed point
  $"Spec"(FF_p)->"Spec"(ZZ)$ does not form a locally constant family over the
  base.
]

=== Finite Étale Algebras over a Ring

#definition(title: "Finite Étale Algebra")[
  Let $A$ be a commutative ring. A commutative $A$-algebra $B$ is
  #emph[finite étale] if the associated morphism

  $ "Spec" B->"Spec" A $

  is finite and étale.
]

#theorem(title: "Algebraic and Fiberwise Characterizations")[
  Let $B$ be a finite $A$-algebra. The following conditions are equivalent.

  + The algebra $B$ is finite étale over $A$.

  + The $A$-module $B$ is finite projective and

    $ Omega_(B slash A)=0 $

  + The $A$-module $B$ is finite projective and, for every prime ideal
    $frak(p) subset.eq A$, the fiber

    $ B ⊗_A kappa(frak(p)) $

    is a finite product of finite separable extensions of
    $kappa(frak(p))$.

]

#proofsketch[
  Finite projectivity is the algebraic form of finite flatness. The vanishing
  of $Omega_(B slash A)$ is the unramified condition. After base change to a
  residue field, the field-theoretic theorem identifies the fibers with finite
  products of separable extensions. Conversely, the fiberwise condition and
  finite projectivity imply that the morphism is étale.
]

#example(title: "Ramification Appears Where Étaleness Fails")[
  The algebra $ZZ[i]=ZZ[T] slash (T^2+1)$ is not étale over $ZZ$ at the prime
  $2$, because the derivative $2T$ vanishes in the fiber over $FF_2$. After
  inverting $2$, however,

  $ ZZ[1/2,i] " is finite étale over " ZZ[1/2] $
]

=== Arithmetic Outlook

#remark(title: "Étale Geometry in Number Theory")[
  Étale morphisms organize several central ideas in arithmetic.

  + #emph[Unramified primes.] Let $L slash K$ be a finite extension of number
    fields. The finite morphism

    $ "Spec"(cal(O)_L)->"Spec"(cal(O)_K) $

    is étale away from the relative discriminant ideal
    $frak(d)_(L slash K)$. At a prime $frak(p)$ outside the discriminant, the
    fiber is a product of finite separable residue-field extensions:

    $ cal(O)_L ⊗_(cal(O)_K) kappa(frak(p)) tilde.eq product_(frak(q)|frak(p)) kappa(frak(q)) $

    Thus étaleness is the scheme-theoretic form of being unramified.

  + #emph[Frobenius.] In a finite Galois extension, the action of Frobenius on
    the geometric fiber above an unramified prime records the residue degrees
    and produces the Frobenius conjugacy class used in decomposition laws,
    Chebotarev's theorem, and Euler factors of $L$-functions.

  + #emph[The étale fundamental group.] For a geometric point
    $overline(eta)$ of $"Spec" K$,

    $ pi_1^"étale" ("Spec" K,overline(eta)) tilde.eq "Gal"(K^"sep" slash K) $

    More generally, finite connected étale covers of a normal connected
    arithmetic scheme correspond to finite extensions unramified along that
    scheme. If $cal(O)_(K,S)$ denotes the ring of $S$-integers, passing to
    $"Spec"(cal(O)_(K,S))$ permits ramification precisely at the primes in
    $S$.

  + #emph[Étale cohomology.] The groups
    $H^i_"étale" (X_(overline(K)),QQ_ell)$ carry continuous Galois actions. They
    connect geometry with Galois representations, Frobenius traces, point
    counts, zeta functions, and arithmetic $L$-functions.

  + #emph[Local-to-global arithmetic.] Étale localization is fine enough to
    split finite separable phenomena but coarse enough to retain arithmetic
    information. It is therefore the natural topology for descent, torsors,
    and cohomological formulations of class field theory. In arithmetic
    geometry, étale means locally unramified, infinitesimally rigid, and stable
    under base change.
]

== Trace and Norm

Trace and norm turn an element upstairs into an element downstairs. They are
defined by linear algebra, computed from conjugates, and interpreted
geometrically by summing or multiplying values along a finite fiber.

#quote[
  Trace is additive integration along a finite fiber; norm is multiplicative
  integration along that fiber.
]

=== Linear-Algebraic Definitions

#definition(title: "Field Trace, Norm, and Characteristic Polynomial")[
  Let $L slash K$ be a finite extension of degree $n$, not necessarily
  separable. For $x in L$, multiplication by $x$ is the $K$-linear map

  $ m_x:L->L, quad y mapsto x y $

  The #emph[trace] and #emph[norm] of $x$ are

  $ "Tr"_(L slash K) (x):="tr"(m_x) $

  $ "N"_(L slash K) (x):=det(m_x) $

  Its characteristic polynomial over $K$ is

  $ chi_(x,L slash K) (T):=det(T "id"_L-m_x) $

  Thus

  $ chi_(x,L slash K) (T)=T^n-"Tr"_(L slash K) (x)T^(n-1)+dots+(-1)^n "N"_(L slash K) (x) $
]

These definitions do not depend on a choice of basis. In practice, choose a
$K$-basis $e_1,dots,e_n$ of $L$, form the multiplication matrix $M_x$ from

$ x e_j=sum_(i=1)^n (M_x)_(i j)e_i $

and compute its trace and determinant.

#proposition(title: "Basic Identities")[
  For $x,y in L$ and $a in K$,

  + trace is $K$-linear:

    $ "Tr"_(L slash K) (x+y)="Tr"_(L slash K) (x)+"Tr"_(L slash K) (y) $

    $ "Tr"_(L slash K) (a x)=a "Tr"_(L slash K) (x) $

  + norm is multiplicative:

    $ "N"_(L slash K) (x y)="N"_(L slash K) (x)"N"_(L slash K) (y) $

  + scalars satisfy

    $ "Tr"_(L slash K) (a)=n a, quad "N"_(L slash K) (a)=a^n $

  + for $x!=0$,

    $ "N"_(L slash K) (x^(-1))="N"_(L slash K) (x)^(-1) $

  + every $K$-automorphism $tau$ of $L$ preserves trace and norm.
]

#proof[
  The identities

  $ m_(x+y)=m_x+m_y, quad m_(a x)=a m_x, quad m_(x y)=m_x compose m_y $

  reduce the first three assertions to the linearity of matrix trace and the
  multiplicativity of determinant. For $a in K$, multiplication by $a$ is the
  scalar matrix $a I_n$. Finally,

  $ m_(tau(x))=tau compose m_x compose tau^(-1) $

  so the two multiplication maps have the same characteristic polynomial.
]

#remark(title: "Trace Is Additive, Norm Is Multiplicative")[
  Norm is generally not additive, and trace is generally not multiplicative.
  The two constructions are parallel only after replacing addition on one side
  by multiplication on the other. Moreover,

  $ "N"_(L slash K) (x)=0 <=> x=0 $

  because $L$ is a field and $m_x$ is invertible exactly when $x!=0$.
]

#theorem(title: "Transitivity in a Tower")[
  For a tower of finite extensions $K subset.eq E subset.eq L$,

  $ "Tr"_(L slash K)="Tr"_(E slash K) compose "Tr"_(L slash E) $

  $ "N"_(L slash K)="N"_(E slash K) compose "N"_(L slash E) $
]

#proofsketch[
  Choose an $E$-basis of $L$ and a $K$-basis of $E$. Multiplication by an
  element of $L$ first gives a matrix over $E$; replacing each entry by its
  multiplication matrix over $K$ produces the full matrix over $K$. Taking
  traces and determinants gives the two formulas.
]

=== Computation from Minimal Polynomials and Conjugates

#proposition(title: "The Minimal-Polynomial Formula")[
  Let $x in L$, put $E=K(x)$, and write

  $ m_(x,K) (T)=T^d+c_(d-1)T^(d-1)+dots+c_0 $

  for the minimal polynomial of $x$ over $K$. If $r=[L:E]$, then

  $ chi_(x,L slash K) (T)=m_(x,K) (T)^r $

  Consequently,

  $ "Tr"_(L slash K) (x)=-r c_(d-1) $

  $ "N"_(L slash K) (x)=((-1)^d c_0)^r $

  In particular, when $L=K(x)$,

  $ "Tr"_(L slash K) (x)=-c_(n-1), quad "N"_(L slash K) (x)=(-1)^n c_0 $
]

#proof[
  As an $E$-vector space, $L$ has dimension $r$, and multiplication by $x$ acts
  as the scalar $x$ on each copy of $E$. Therefore its characteristic
  polynomial over $K$ is the $r$-th power of the characteristic polynomial of
  multiplication by $x$ on $E$. Since $E=K(x)$, the latter is precisely
  $m_(x,K)$. Comparing the coefficient of $T^(n-1)$ and the constant term gives
  the formulas.
]

#theorem(title: "The Conjugate Formula")[
  Suppose that $L slash K$ is separable of degree $n$. If
  $sigma_1,dots,sigma_n:L->overline(K)$ are its $K$-embeddings, then

  $ chi_(x,L slash K) (T)=product_(i=1)^n (T-sigma_i (x)) $

  and hence

  $ "Tr"_(L slash K) (x)=sum_(i=1)^n sigma_i (x) $

  $ "N"_(L slash K) (x)=product_(i=1)^n sigma_i (x) $
]

#proof[
  After base change to $overline(K)$, the étale algebra
  $L ⊗_K overline(K)$ becomes $overline(K)^n$. Multiplication by $x$ becomes the
  diagonal operator with entries $sigma_1 (x),dots,sigma_n (x)$. The formulas are
  its characteristic polynomial, trace, and determinant.
]

#corollary(title: "Trace Pairing and Discriminant")[
  For a finite extension $L slash K$, the trace pairing

  $ L times L->K, quad (x,y) mapsto "Tr"_(L slash K) (x y) $

  is nondegenerate if and only if $L slash K$ is separable. Hence, for any
  $K$-basis $b_1,dots,b_n$ of $L$, the discriminant

  $ "disc"(b_1,dots,b_n):=det("Tr"_(L slash K) (b_i b_j))_(1<=i,j<=n) $

  is nonzero exactly when $L slash K$ is separable.
]

#proof[
  In the separable case, base change to $overline(K)$ identifies the pairing
  with the ordinary dot product on $overline(K)^n$. In the inseparable case,
  $L ⊗_K overline(K)$ has a nonzero nilpotent $z$. For every $b$, the operator
  $m_(z b)$ is nilpotent, so its trace is zero. Thus $z$ lies in the radical of
  the base-changed trace pairing, which must be degenerate.
]

#example(title: "Quadratic Extensions")[
  Assume $"char"(K)!=2$ and let $L=K(sqrt(d))$, where $d$ is not a square. The
  two embeddings send $sqrt(d)$ to $plus.minus sqrt(d)$. Hence

  $ "Tr"_(L slash K) (a+b sqrt(d))=2a $

  $ "N"_(L slash K) (a+b sqrt(d))=a^2-d b^2 $

  In particular, for $L=QQ(sqrt(-5))$,

  $ "N"_(L slash QQ) (a+b sqrt(-5))=a^2+5b^2 $

  This is the norm calculation used earlier to show that
  $(2,1+sqrt(-5))$ is not principal.
]

#example(title: "Finite Fields")[
  The embeddings of $FF_(q^n)$ over $FF_q$ are the powers of Frobenius. Thus

  $ "Tr"_(FF_(q^n) slash FF_q) (x)=x+x^q+dots+x^(q^(n-1)) $

  $ "N"_(FF_(q^n) slash FF_q) (x)=x^(1+q+dots+q^(n-1))=x^((q^n-1)/(q-1)) $

  for $x!=0$. The norm is a surjective homomorphism
  $FF_(q^n)^times->FF_q^times$.
]

#example(title: "The Purely Inseparable Contrast")[
  Let $K=FF_p (t)$ and $L=K(u)$ with $u^p=t$. For every $x in L$,

  $ chi_(x,L slash K) (T)=(T-x)^p=T^p-x^p $

  Thus

  $ "Tr"_(L slash K) (x)=0, quad "N"_(L slash K) (x)=x^p $

  The trace pairing is identically zero. This illustrates why separability is
  exactly the condition needed for a nondegenerate trace pairing.
]

=== Finite Locally Free Algebras

#definition(title: "Trace and Norm over a Ring")[
  Let $B$ be a finite locally free $A$-algebra of constant rank $n$. For
  $b in B$, multiplication defines an $A$-linear endomorphism

  $ m_b:B->B $

  Its trace and determinant define

  $ "Tr"_(B slash A) (b):="tr"(m_b) in A $

  $ "N"_(B slash A) (b):=det(m_b) in A $

  These definitions make sense for finite projective modules because trace and
  determinant may be checked after localization, where $B$ is free.
]

#proposition(title: "Formulas over a Ring")[
  Let $B$ be finite locally free of rank $n$ over $A$.

  + The trace map $B->A$ is $A$-linear, while norm gives a multiplicative map
    $B->A$.

  + For $a in A$,

    $ "Tr"_(B slash A) (a)=n a, quad "N"_(B slash A) (a)=a^n $

  + An element $b in B$ is a unit if and only if $"N"_(B slash A) (b)$ is a
    unit in $A$.

  + For finite locally free algebras $B_1$ and $B_2$,

    $ "Tr"_((B_1 times B_2) slash A) (b_1,b_2)="Tr"_(B_1 slash A) (b_1)+"Tr"_(B_2 slash A) (b_2) $

    $ "N"_((B_1 times B_2) slash A) (b_1,b_2)="N"_(B_1 slash A) (b_1)"N"_(B_2 slash A) (b_2) $

  + Trace, norm, and characteristic polynomial commute with arbitrary base
    change. For an $A$-algebra $A'$,

    $ "Tr"_((B ⊗_A A') slash A') (b ⊗ 1)="Tr"_(B slash A) (b) ⊗ 1 $

    $ "N"_((B ⊗_A A') slash A') (b ⊗ 1)="N"_(B slash A) (b) ⊗ 1 $
]

#proofsketch[
  All assertions are local on $"Spec" A$, so one may choose a basis of $B$.
  They then follow from the corresponding matrix identities. For the unit
  criterion, $m_b$ is invertible exactly when its determinant is a unit; if
  $m_b$ is invertible, applying its inverse to $1$ produces an inverse of $b$.
]

#block(breakable: false)[
  #theorem(title: "The Trace Criterion for Finite Étale Algebras")[
    Let $B$ be finite locally free over $A$. Then $B$ is finite étale over $A$
    if and only if the trace pairing is perfect; equivalently, the map

    $ B->Hom_A (B,A), quad b mapsto (c mapsto "Tr"_(B slash A) (b c)) $

    is an isomorphism.
  ]
]

#proofsketch[
  The displayed map is a map between finite locally free modules of the same
  rank, so it is an isomorphism exactly when it is an isomorphism on every
  residue-field fiber. Over a field, a finite commutative algebra becomes a
  product of local Artin algebras after passing to an algebraic closure. Its
  trace pairing is perfect exactly when every local factor has length one,
  that is, exactly when the algebra is a product of finite separable fields.
  The fiberwise characterization of finite étale algebras now gives the
  result.
]

=== Geometric Meaning along Finite Fibers

Let $f:X->S$ be a finite locally free morphism of constant degree $n$. The
sheaf $f_* cal(O)_X$ is a rank-$n$ vector bundle on $S$. Multiplication by a
regular function $b$ on $X$ is an endomorphism of this vector bundle, and its
trace and determinant are regular functions on $S$:

$ "Tr"_f (b), "N"_f (b) in Gamma(S,cal(O)_S) $

#theorem(title: "Fiberwise Sum and Product")[
  Let $overline(s)->S$ be a geometric point. Write the finite geometric fiber as
  a collection of points $x in X_(overline(s))$, and let $ell_x$ be the length
  of the local Artin ring at $x$. Then

  $ "Tr"_f (b) (overline(s))=sum_(x in X_(overline(s))) ell_x b(x) $

  $ "N"_f (b) (overline(s))=product_(x in X_(overline(s))) b(x)^(ell_x) $

  If $f$ is finite étale, every $ell_x=1$, so its geometric fibers consist of
  $n$ distinct points and

  $ "Tr"_f (b) (overline(s))=sum_(x in X_(overline(s))) b(x), quad "N"_f (b) (overline(s))=product_(x in X_(overline(s))) b(x) $
]

#proof[
  Trace and norm commute with base change, so it is enough to work over the
  algebraically closed residue field of $overline(s)$. The coordinate algebra
  of the fiber is a product of local Artin algebras. On the factor supported at
  $x$, write $b=b(x)+nu$, where $nu$ is nilpotent. Multiplication by $b$ is the
  scalar operator $b(x)$ plus a nilpotent operator. Its trace is
  $ell_x b(x)$ and its determinant is $b(x)^(ell_x)$. Summing traces and
  multiplying determinants over the factors gives the formulas.
]

#block(breakable: false)[
  #remark(title: "What the Multiplicities Remember")[
    For a finite étale map, trace and norm literally sum and multiply over the
    distinct points of a fiber. For a ramified or nonreduced fiber, the same
    point is counted with its scheme-theoretic length. Thus the linear-algebraic
    multiplicity in the characteristic polynomial is exactly the geometric
    multiplicity of the fiber.
  ]
]

#proposition(title: "Norm and Pushforward of Divisors")[
  Let $f:X->Y$ be a finite dominant morphism of normal integral curves, with
  function-field extension $K(X) slash K(Y)$. For $g in K(X)^times$,

  $ "div"_Y ("N"_(K(X) slash K(Y)) (g))=f_* "div"_X (g) $

  Here the pushforward of a closed point is

  $ f_*[x]=[kappa(x):kappa(f(x))][f(x)] $

  Equivalently, for a closed point $y in Y$,

  $ v_y ("N"_(K(X) slash K(Y)) (g))=sum_(x in X, f(x)=y) [kappa(x):kappa(y)]v_x (g) $
]

#remark[
  This identity says that the norm pushes zeros and poles down the map. It also
  extends from rational functions to a norm homomorphism on line bundles,

  $ "Nm"_f:"Pic"(X)->"Pic"(Y) $

  whose effect on divisor classes is induced by $f_*$. Trace is the additive
  pushforward on functions; norm is its multiplicative companion.
]

=== Arithmetic Consequences

#proposition(title: "Integrality and Principal Ideals")[
  Let $L slash K$ be a finite extension of number fields. If
  $alpha in cal(O)_L$, then

  $ "Tr"_(L slash K) (alpha), "N"_(L slash K) (alpha) in cal(O)_K $

  For $K=QQ$ and $0!=alpha in cal(O)_L$,

  $ |cal(O)_L slash alpha cal(O)_L|=|"N"_(L slash QQ) (alpha)| $

  Thus the absolute norm of the principal ideal $(alpha)$ is the absolute value
  of the field norm of $alpha$.
]

#proof[
  The conjugates of an algebraic integer are algebraic integers, so their sum
  and product are integral over $cal(O)_K$. They also lie in $K$; since
  $cal(O)_K$ is integrally closed, they lie in $cal(O)_K$. For the second
  formula, multiplication by $alpha$ is an injective endomorphism of the
  lattice $cal(O)_L$. The index of its image is the absolute value of its
  determinant, which is $|"N"_(L slash QQ) (alpha)|$.
]
