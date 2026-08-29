#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Dedekind Extensions

The local structure of a Dedekind domain is stable under finite separable
extensions, but proving this requires a global finiteness argument. Dual
modules and lattices provide exactly that argument: the trace pairing places
the integral closure between two finite lattices. Once the new ring is known
to be Dedekind, unique factorization of ideals describes how every prime
splits upstairs.

== Dual Modules and Pairings

Duality reverses arrows and exchanges a rank-one object with its inverse. This
is already familiar for fractional ideals, and it is the same operation that
appears geometrically in the Picard group.

#definition(title: "Dual Module and Dual Homomorphism")[
  Let $A$ be a commutative ring and let $M$ be an $A$-module. The #emph[dual
  module] of $M$ is

  $ M^∨:=Hom_A (M,A) $

  For an $A$-linear map $phi:M->N$, its #emph[dual map] is

  $ phi^∨:N^∨->M^∨, quad g mapsto g compose phi $

  Thus duality is a contravariant functor

  $ (-)^∨:"Mod"_A^"op"->"Mod"_A $
]

The reversal of arrows follows from

$ (psi compose phi)^∨=phi^∨ compose psi^∨ $

There is also a canonical evaluation map

$ "ev"_M:M->(M^∨)^∨, quad m mapsto (f mapsto f(m)) $

An $A$-module is #emph[reflexive] if this map is an isomorphism.

#proposition(title: "Basic Properties of Dual Modules")[
  Let $M$ and $N$ be $A$-modules.

  + Finite direct sums commute with duality:

    $ (M ⊕ N)^∨ tilde.eq M^∨ ⊕ N^∨ $

  + If $M$ is finite projective, then $M^∨$ is finite projective and the
    evaluation map is an isomorphism:

    $ M tilde.eq (M^∨)^∨ $

  + If $M$ is free with basis $e_1,dots,e_n$, then $M^∨$ has the unique dual
    basis $e_1^∨,dots,e_n^∨$ satisfying

    $ e_i^∨ (e_j)=delta_(i j) $
]

#proof[
  A map $M ⊕ N->A$ is uniquely determined by its restrictions to the
  two summands, which proves the first assertion. The remaining assertions are
  immediate for a finite free module. A finite projective module is locally
  finite free, and a map between finite projective modules is an isomorphism
  exactly when it is so after localization at every prime. The free case
  therefore proves the projective case.
]

#example(title: "Why Finiteness Matters")[
  As a $ZZ$-module, $QQ^∨=0$: every homomorphism $QQ->ZZ$ is zero because $QQ$
  is divisible and $ZZ$ has no nonzero divisible subgroup. Hence
  $(QQ^∨)^∨=0$, so the evaluation map is very far from an isomorphism. Finite
  projectivity, rather than duality alone, is what makes double dualization
  recover the original module.
]

#proposition(title: "The Dual of a Fractional Ideal")[
  Let $A$ be a domain with fraction field $K$, and let $I subset.eq K$ be a
  nonzero $A$-submodule. Multiplication induces a canonical isomorphism

  $ (A:I):={x in K | x I subset.eq A} tilde.eq I^∨ $

  If $I$ is an invertible fractional ideal, then

  $ I^∨ tilde.eq I^(-1), quad (I^∨)^∨ tilde.eq I $
]

#proof[
  Every $x in (A:I)$ defines the functional $m mapsto x m$. Conversely, choose
  $0!=a in I$. If $f:I->A$ is $A$-linear, tensoring with $K$ gives a $K$-linear
  endomorphism of $K ⊗_A I tilde.eq K$. It is multiplication by
  $f(a)/a$, and therefore

  $ f(m)=f(a)/a dot m $

  for every $m in I$. Hence $f$ is multiplication by $f(a)/a in (A:I)$. The
  two constructions are inverse. For an invertible ideal,
  $(A:I)=I^(-1)$, and dualizing once more gives $I$.
]

#remark(title: "The Picard-Group Analogy")[
  Let $X="Spec" A$. A finite projective module $P$ of rank one determines a
  line bundle $tilde(P)$ on $X$, and its module dual determines the dual line
  bundle

  $ tilde(P^∨) tilde.eq "Hom"_(cal(O)_X) (tilde(P),cal(O)_X) $

  Evaluation gives

  $ tilde(P) ⊗_(cal(O)_X) tilde(P^∨) tilde.eq cal(O)_X $

  so dualization is inversion in the Picard group:

  $ [tilde(P^∨)]=-[tilde(P)] " in " "Pic"(X) $

  For a Dedekind domain, a fractional ideal $I$ is a rank-one projective
  module and $I^∨ tilde.eq I^(-1)$. Under
  $"Cl"(A) tilde.eq "Pic"(X)$, the passage $I mapsto I^∨$ is therefore exactly
  the passage from an ideal class to its inverse.
]

#definition(title: "Pairings: Nondegenerate versus Perfect")[
  An $A$-bilinear pairing on $M$ is a map

  $ beta:M times M->A $

  It induces an $A$-linear map

  $ lambda_beta:M->M^∨, quad x mapsto (y mapsto beta(x,y)) $

  The pairing is #emph[nondegenerate] if $lambda_beta$ is injective and
  #emph[perfect] if $lambda_beta$ is an isomorphism.
]

#remark(title: "Nondegenerate Need Not Mean Perfect")[
  On a finite-dimensional vector space over a field, injectivity and
  bijectivity are equivalent, so a nondegenerate pairing is perfect. Over a
  general ring they differ. The pairing

  $ beta:ZZ times ZZ->ZZ, quad (x,y) mapsto 2 x y $

  is nondegenerate, but the induced map $ZZ->ZZ^∨ tilde.eq ZZ$ has image
  $2ZZ$ and is not surjective.
]

== Lattices and Dual Lattices

Let $A$ be a domain with fraction field $K$, and let $V$ be a finite-dimensional
$K$-vector space. A lattice is an integral structure inside $V$: it remembers
which vectors should count as having integral coordinates without requiring a
preferred basis.

#definition(title: "Full Lattice")[
  An #emph[$A$-lattice] in $V$ is a finitely generated $A$-submodule
  $M subset.eq V$ such that

  $ K M=V $

  Equivalently, the natural map

  $ K ⊗_A M->V $

  is an isomorphism. We always use lattice to mean a full lattice.
]

#remark(title: "A Lattice Need Not Be Free")[
  If $A$ is a PID, every lattice is finite free because it is finitely
  generated and torsion-free. Over a nonprincipal Dedekind domain, lattices
  need not be free. A nonprincipal fractional ideal is already a rank-one
  lattice in $K$: it is projective and locally free, but it has no global
  basis. This is precisely the phenomenon measured by $"Pic"("Spec" A)$.
]

#block(breakable: false)[
  #proposition(title: "Commensurability of Lattices")[
    If $M$ and $N$ are two $A$-lattices in $V$, then there exist nonzero
    $a,b in A$ such that

    $ a M subset.eq N, quad b N subset.eq M $

    Thus any two lattices differ only by bounded denominators.
  ]
]

#proof[
  Choose generators of $M$ and express them in terms of elements of $N$ that
  span $V$ over $K$. Clearing the finitely many denominators gives
  $0!=a in A$ with $a M subset.eq N$. Interchanging $M$ and $N$ gives $b$.
]

#definition(title: "Dual Lattice")[
  Assume now that $A$ is Noetherian and that $V$ carries a perfect
  $K$-bilinear pairing

  $ beta:V times V->K $

  For an $A$-lattice $M subset.eq V$, its #emph[dual lattice] with respect to
  $beta$ is

  $ M^∗:={x in V | beta(x,M) subset.eq A} $
]

#theorem(title: "The Dual Lattice Is the Dual Module")[
  The module $M^∗$ is an $A$-lattice in $V$, and the map

  $ M^∗->M^∨, quad x mapsto (m mapsto beta(x,m)) $

  is an isomorphism.
]

#proof[
  Choose a $K$-basis $e_1,dots,e_n$ contained in $M$, and let
  $e_1^∗,dots,e_n^∗$ be its dual basis for $beta$. Put

  $ N=A e_1+dots+A e_n $

  Since $M$ is finitely generated, clearing denominators gives $0!=d in A$
  such that

  $ N subset.eq M subset.eq 1/d N $

  Reversing inclusions under duality gives

  $ d N^∗ subset.eq M^∗ subset.eq N^∗ $

  The module $N^∗=A e_1^∗+dots+A e_n^∗$ is finite free. Since $A$ is
  Noetherian, its submodule $M^∗$ is finitely generated; because it contains
  $d N^∗$, it spans $V$. Hence $M^∗$ is a lattice.

  The displayed map is injective because $M$ spans $V$ and $beta$ is
  nondegenerate. For surjectivity, tensor $f in M^∨$ with $K$ to obtain a
  functional $f_K:V->K$. Perfection of $beta$ gives a unique $x in V$ such
  that $f_K (m)=beta(x,m)$. Since $f(M) subset.eq A$, this $x$ lies in $M^∗$.
]

#proposition(title: "Localization and Biduality")[
  Let $S subset.eq A$ be multiplicatively closed. Then

  $ (S^(-1) M)^∗=S^(-1) (M^∗) $

  If $A$ is Dedekind and $beta$ is symmetric, then every $A$-lattice satisfies

  $ (M^∗)^∗=M $
]

#proof[
  One inclusion in the localization formula is immediate. For the other,
  choose finitely many generators $m_i$ of $M$. If
  $x in (S^(-1)M)^∗$, clear the finitely many denominators occurring in
  $beta(x,m_i)$ to find $s in S$ with $s x in M^∗$.

  For biduality, equality can be checked after localization at every nonzero
  prime $frak(p)$. The ring $A_(frak(p))$ is a DVR, so the localized lattice is
  free. A basis and its dual basis show directly that the double dual equals
  the original free lattice. The localization formula then gives the global
  equality.
]

#example(title: "Trace-Dual Lattices")[
  Let $L slash K$ be a finite separable extension. The trace pairing

  $ beta(x,y)="Tr"_(L slash K) (x y) $

  is symmetric and perfect. For an $A$-lattice $M subset.eq L$, its trace dual
  is therefore

  $ M^∗={x in L | "Tr"_(L slash K) (x M) subset.eq A} $

  This construction will control the size of the integral closure of $A$ in
  $L$.
]

== Dedekind Extensions

#definition(title: "Integral Closure and the Dedekind-Extension Setup")[
  Let $A$ be a domain with fraction field $K$, and let $L slash K$ be a finite
  extension. An element $x in L$ is #emph[integral over $A$] if it satisfies a
  monic polynomial in $A[T]$. The #emph[integral closure] of $A$ in $L$ is

  $ B={x in L | x " is integral over " A} $

  In this section we use the following setup:

  + $A$ is a Dedekind domain with fraction field $K$;

  + $L slash K$ is finite and separable;

  + $B$ is the integral closure of $A$ in $L$.

  The extension $B slash A$ will be called a #emph[finite separable Dedekind
  extension].
]

The set $B$ is a subring of $L$. The important point is not integral
closedness, which is built into the definition, but finite generation over
$A$.

#proposition(title: "Clearing Denominators in a Finite Extension")[
  Every $x in L$ can be written as

  $ x=b/a $

  for some $b in B$ and $0!=a in A$. Consequently,

  $ K B=L, quad "Frac"(B)=L $
]

#proof[
  Let

  $ f(T)=T^n+c_(n-1)T^(n-1)+dots+c_0 in K[T] $

  be the minimal polynomial of $x$. Choose $0!=a in A$ such that
  $a c_i in A$ for every $i$. The element $a x$ satisfies the monic polynomial

  $ T^n+a c_(n-1)T^(n-1)+a^2 c_(n-2)T^(n-2)+dots+a^n c_0 $

  in $A[T]$. Thus $b=a x$ belongs to $B$ and $x=b/a$. It follows that $B$
  spans $L$ over $K$ and that every element of $L$ is a quotient of two
  elements of $B$.
]

#lemma(title: "Trace and Norm Preserve Integrality")[
  For every $b in B$,

  $ "Tr"_(L slash K) (b) in A, quad "N"_(L slash K) (b) in A $
]

#proof[
  The minimal polynomial $m_(b,K)$ lies in $A[T]$. Indeed, its roots in a
  splitting field are integral over $A$, so its coefficients are integral over
  $A$; the coefficients also lie in $K$, and $A$ is integrally closed in $K$.
  The minimal-polynomial formulas for trace and norm express them in terms of
  these coefficients, and therefore put both elements in $A$.
]

#theorem(title: "The Integral Closure Is a Lattice")[
  In the Dedekind-extension setup, $B$ is an $A$-lattice in $L$. In
  particular, it is a finite $A$-module of rank $[L:K]$.
]

#proof[
  By the denominator-clearing proposition, $B$ spans $L$. Choose a $K$-basis
  $e_1,dots,e_n$ of $L$ contained in $B$, and set

  $ M=A e_1+dots+A e_n subset.eq B $

  Use the perfect trace pairing on $L$ and define

  $ B^∗={x in L | "Tr"_(L slash K) (x B) subset.eq A} $

  If $b,c in B$, then $b c in B$, so the preceding lemma gives
  $"Tr"_(L slash K) (b c) in A$. Hence $B subset.eq B^∗$. Since
  $M subset.eq B$, duality reverses containment and gives

  $ M subset.eq B subset.eq B^∗ subset.eq M^∗ $

  The dual-lattice theorem says that $M^∗$ is a finite $A$-module. Since $A$
  is Noetherian, its submodule $B$ is finitely generated. Together with
  $K B=L$, this proves that $B$ is an $A$-lattice. Its rank is
  $dim_K (L)=[L:K]$.
]

#quote[
  The trace pairing traps the integral closure between two lattices; this is
  the finiteness mechanism behind Dedekind extensions.
]

#lemma(title: "Dimension under an Integral Extension")[
  Let $C slash A$ be an integral extension of domains. If
  $frak(q)_0 subset frak(q)_1$ are prime ideals of $C$, then

  $ frak(q)_0 inter A subset frak(q)_1 inter A $

  In particular, $dim(C)<=dim(A)$.
]

#proof[
  Suppose the two contractions were equal to $frak(p)$. The domain
  $C slash frak(q)_0$ is integral over $A slash frak(p)$. After inverting all
  nonzero elements of $A slash frak(p)$, it becomes an algebraic domain over
  the field $"Frac"(A slash frak(p))$, hence a field. But
  $frak(q)_1 slash frak(q)_0$ is disjoint from these denominators and would
  localize to a nonzero proper prime ideal of that field, a contradiction.
  Thus strict chains contract to strict chains.
]

#theorem(title: "Integral Closures of Dedekind Domains")[
  Let $A$ be a Dedekind domain with fraction field $K$, let $L slash K$ be a
  finite separable extension, and let $B$ be the integral closure of $A$ in
  $L$. Then $B$ is a Dedekind domain with fraction field $L$.
]

#proof[
  We verify the three defining properties.

  + The ring $B$ is integrally closed in $L$. If $x in L$ is integral over
    $B$, then transitivity of integrality makes $x$ integral over $A$, so
    $x in B$.

  + The ring $B$ is Noetherian. It is finite over the Noetherian ring $A$ by
    the lattice theorem, and every finite algebra over a Noetherian ring is
    Noetherian.

  + We have $dim(B)<=dim(A)=1$ by the dimension lemma. Moreover, $B$ is not a
    field. Indeed, $B inter K=A$ because $A$ is integrally closed in $K$; if
    $B$ were a field, it would contain $K$ and force $K=B inter K=A$.
    Therefore $dim(B)=1$.

  Finally, the denominator-clearing proposition gives $"Frac"(B)=L$.
]

#remark(title: "What Separability Is Doing")[
  Separability makes the trace pairing perfect, which proves that $B$ is
  finite over $A$. The conclusion that the integral closure is Dedekind also
  holds for arbitrary finite extensions, but in the inseparable case its
  Noetherianity requires the deeper Krull--Akizuki theorem; the integral
  closure need not be finite as an $A$-module.
]

== Splitting Primes

Continue with the Dedekind-extension setup, and let $n=[L:K]$. Since $B$ is
Dedekind, the extension of a nonzero prime ideal $frak(p) subset.eq A$ is
nonzero. It is also proper: $B_(frak(p))$ is free of positive rank over the DVR
$A_(frak(p))$, so its reduction modulo $frak(p)$ is nonzero. It therefore has
a unique prime-ideal factorization. Write $frak(q)|frak(p)$ for the primes that
occur, so

$ frak(p)B=product_(frak(q)|frak(p)) frak(q)^(e_(frak(q))) $

The primes in this product are the points of $"Spec" B$ lying over the point
$frak(p)$ of $"Spec" A$.

#proposition(title: "Primes Lying Above a Prime")[
  For a nonzero prime $frak(q) subset.eq B$ and a nonzero prime
  $frak(p) subset.eq A$, the following are equivalent:

  + $frak(q)$ occurs in the factorization of $frak(p)B$;

  + $frak(q)$ contains $frak(p)B$;

  + $frak(q) inter A=frak(p)$.

  In this case we write $frak(q)|frak(p)$ and say that $frak(q)$ #emph[lies
  above] $frak(p)$.
]

#proof[
  In a Dedekind domain, a prime divides an integral ideal exactly when it
  contains that ideal, so the first two conditions are equivalent. If
  $frak(p)B subset.eq frak(q)$, then
  $frak(p) subset.eq frak(q) inter A$; maximality of $frak(p)$ forces equality.
  Conversely, $frak(q) inter A=frak(p)$ implies
  $frak(p)B subset.eq frak(q)$.
]

#block(breakable: false)[
  #definition(title: "Ramification Index and Residue Degree")[
    Let $frak(q)|frak(p)$. The exponent

    $ e_(frak(q) slash frak(p)):=v_(frak(q)) (frak(p)B) $

    is the #emph[ramification index]. The inclusion $A->B$ induces an extension
    of residue fields

    $ kappa(frak(p)):=A slash frak(p) -> kappa(frak(q)):=B slash frak(q) $

    Its degree

    $ f_(frak(q) slash frak(p)):=[kappa(frak(q)):kappa(frak(p))] $

    is the #emph[residue degree] or #emph[inertia degree]. We also put

    $ g_(frak(p)):=abs({frak(q) : frak(q)|frak(p)}) $
  ]
]

#block(breakable: false)[
  #theorem(title: "The Fundamental Identity")[
    For every nonzero prime $frak(p)$ of $A$,

    $ sum_(frak(q)|frak(p)) e_(frak(q) slash frak(p)) f_(frak(q) slash frak(p))=[L:K] $
  ]
]

#proof[
  First compute the dimension of the fiber algebra. Localizing at $frak(p)$,
  the module $B_(frak(p))$ is finite and torsion-free over the DVR
  $A_(frak(p))$, hence free. Its rank is $n$ because
  $K ⊗_A B tilde.eq L$. Therefore

  $ dim_(kappa(frak(p))) (B slash frak(p)B)=n $

  On the other hand, the prime powers in the factorization of $frak(p)B$ are
  pairwise coprime, so the Chinese remainder theorem gives

  $ B slash frak(p)B tilde.eq product_(frak(q)|frak(p)) (B slash frak(q)^(e_(frak(q) slash frak(p)))) $

  For $e=e_(frak(q) slash frak(p))$, the filtration by powers of $frak(q)$ has
  $e$ successive quotients, each one-dimensional over $kappa(frak(q))$.
  Hence

  $ dim_(kappa(frak(p))) (B slash frak(q)^e)=e f_(frak(q) slash frak(p)) $

  Taking dimensions in the product decomposition proves the identity.
]

#block(breakable: false)[
  #definition(title: "Ramified, Inert, and Split Primes")[
    Let $frak(p)$ be a nonzero prime of $A$.

    + The extension is #emph[unramified at $frak(q)|frak(p)$] if
      $e_(frak(q) slash frak(p))=1$ and
      $kappa(frak(q)) slash kappa(frak(p))$ is separable. It is unramified above
      $frak(p)$ if this holds for every $frak(q)|frak(p)$.

    + The prime $frak(p)$ is #emph[inert] if $frak(p)B$ is prime and the
      extension is unramified there. Equivalently,
      $g_(frak(p))=1$, $e=1$, and $f=n$.

    + The prime $frak(p)$ #emph[splits completely] if
      $g_(frak(p))=n$; equivalently, $e=f=1$ for every prime above it.

    + The prime $frak(p)$ is #emph[totally ramified] if there is one prime above
      it with $e=n$; the fundamental identity then forces $f=1$.
  ]
]

#block(breakable: false)[
  #align(center, table(
    columns: (1.05fr, 1.35fr, 1.85fr),
    align: (center, center, center),
    inset: (x: 10pt, y: 5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[Behavior]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Prime data]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Fiber picture]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    table.vline(x: 2, stroke: 0.75pt + c-thm),
    [split completely], [$g=n$, all $e=f=1$], [many distinct rational points],
    [inert], [$g=1$, $e=1$, $f=n$], [one reduced point with a larger residue field],
    [totally ramified], [$g=1$, $e=n$, $f=1$], [one point of multiplicity $n$],
    [mixed], [$sum e f=n$], [several points with varying degrees and lengths],
  ))
]

#remark(title: "The Geometric Fiber")[
  Put $X:="Spec" B$, $Y:="Spec" A$, and let $pi:X->Y$ be the morphism
  induced by $A->B$. The extended ideal $frak(p)B$, or equivalently the ideal
  sheaf $frak(p)cal(O)_X$, is the ideal-theoretic pullback of $frak(p)$. It
  cuts out the #emph[scheme-theoretic fiber] above $frak(p)$:

  $ X times_Y "Spec"(kappa(frak(p))) tilde.eq "Spec"(B slash frak(p)B)=V_X (frak(p)B) $

  Thus $frak(p)B$ means more than just the set of primes above $frak(p)$: the
  ideal also remembers the infinitesimal thickness of the fiber. Indeed, the
  factorization of $frak(p)B$ and the Chinese remainder theorem give

  $ B slash frak(p)B tilde.eq product_(frak(q)|frak(p)) B slash frak(q)^(e_(frak(q) slash frak(p))) $

  The underlying points of this fiber are precisely the
  $frak(q)|frak(p)$. Its component at $frak(q)$ is a thickened point of length
  $e_(frak(q) slash frak(p))$ over its residue field $kappa(frak(q))$. The
  residue degree $f_(frak(q) slash frak(p))$ measures how far that point is
  from being $kappa(frak(p))$-rational. Consequently, its contribution to the
  degree of the whole fiber is $e_(frak(q) slash frak(p))
  f_(frak(q) slash frak(p))$, and

  $ B ⊗_A kappa(frak(p)) tilde.eq B slash frak(p)B $

  has total dimension $[L:K]$ over $kappa(frak(p))$.

  There is an equivalent divisor picture. A nonzero prime $frak(p)$ is a
  closed point, hence a prime divisor, on the arithmetic curve $Y$. Pulling it
  back to $X$ gives

  $ pi^* [frak(p)]=sum_(frak(q)|frak(p)) e_(frak(q) slash frak(p))[frak(q)] $

  In other words, the ideal identity
  $frak(p)B=product_(frak(q)|frak(p))
  frak(q)^(e_(frak(q) slash frak(p)))$ is exactly the divisor-theoretic
  statement that the point $frak(p)$ pulls back to the points above it,
  counted with ramification multiplicity. Notice that the residue degrees
  $f_(frak(q) slash frak(p))$ do not appear as divisor coefficients; they
  record the degrees of the resulting points instead.

  The fiber is finite étale exactly when every $e=1$ and every residue-field
  extension is separable. If $kappa(frak(p))$ is perfect, as it is for a finite
  field, this reduces to the condition $e=1$ for every prime above
  $frak(p)$.
]

#example(title: [Splitting in $ZZ[i] slash ZZ$])[
  Let $A=ZZ$, $B=ZZ[i]$, and $L=QQ(i)$. The behavior of a rational prime is
  determined by the factorization of $T^2+1$ modulo $p$.

  + The prime $2$ is totally ramified:

    $ (2)=(1+i)^2 $

  + If $p equiv 1 mod 4$, then $-1$ is a square modulo $p$. Choosing
    $a^2 equiv -1 mod p$ gives two distinct primes

    $ (p)=(p,i-a)(p,i+a) $

    so $p$ splits completely.

  + If $p equiv 3 mod 4$, then $T^2+1$ is irreducible modulo $p$, so $(p)$ is
    inert and its residue degree is $2$.

  In all three cases the identity $sum e f=2=[QQ(i):QQ]$ is visible directly.
]

== Rings of Integers

#block(breakable: false)[
  #definition(title: "Algebraic Integers and the Ring of Integers")[
    An algebraic number $alpha in overline(QQ)$ is an #emph[algebraic integer]
    if it is integral over $ZZ$, equivalently, if it is a root of a monic
    polynomial in $ZZ[T]$.

    A #emph[number field] is a finite extension $K slash QQ$. Its #emph[ring of
    integers] is

    $ cal(O)_K:={alpha in K | alpha " is integral over " ZZ} $

    Thus $cal(O)_K$ is the integral closure of $ZZ$ in $K$.
  ]
]

#theorem(title: "The Ring of Integers Is Dedekind")[
  For every number field $K$, the ring $cal(O)_K$ is a Dedekind domain with
  fraction field $K$. Moreover, if $n=[K:QQ]$, then $cal(O)_K$ is a free
  $ZZ$-module of rank $n$.
]

#proof[
  The ring $ZZ$ is a Dedekind domain with fraction field $QQ$. Every finite
  extension of $QQ$ is separable because $"char"(QQ)=0$. The theorem on
  integral closures of Dedekind domains therefore applies to the integral
  closure $cal(O)_K$ of $ZZ$ in $K$, proving that it is Dedekind and has
  fraction field $K$.

  The lattice theorem makes $cal(O)_K$ a finitely generated $ZZ$-module that
  spans $K$ over $QQ$. It is torsion-free because it lies in the field $K$.
  Every finitely generated torsion-free module over the PID $ZZ$ is free, and
  its rank is

  $ dim_QQ (QQ ⊗_ZZ cal(O)_K)=dim_QQ (K)=n $
]

#remark(title: "What the Theorem Buys Us")[
  Every nonzero ideal of $cal(O)_K$ factors uniquely into prime ideals, every
  localization $(cal(O)_K)_(frak(p))$ is a DVR, and the class group measures
  the failure of principal factorization. Thus the entire ideal-theoretic
  framework of Chapter 1 applies uniformly to every number field.
]

#block(breakable: true)[
  #lemma(title: "Trace and Norm Criterion for Quadratic Fields")[
    Let $K slash QQ$ be a quadratic extension. For $alpha in K$, let
    $overline(alpha)$ denote its image under the nontrivial
    $QQ$-automorphism of $K$. Then

    $ alpha in cal(O)_K <=> "Tr"_(K slash QQ) (alpha) in ZZ " and " "N"_(K slash QQ) (alpha) in ZZ $
  ]

  #proof[
    The two conjugates of $alpha$ are $alpha$ and $overline(alpha)$, so

    $ (T-alpha)(T-overline(alpha))=T^2-(alpha+overline(alpha))T+alpha overline(alpha) $

    $ =T^2-"Tr"_(K slash QQ) (alpha)T+"N"_(K slash QQ) (alpha) $

    Suppose first that $alpha$ is integral. Its conjugate $overline(alpha)$ is
    integral as well, because a $QQ$-automorphism preserves every polynomial
    in $ZZ[T]$. Hence the trace and norm are rational algebraic integers, and
    therefore lie in $ZZ$. Here we use the elementary fact that a rational
    algebraic integer is an integer: applying the rational-root argument to a
    reduced fraction shows that its denominator is $1$.

    Conversely, if the trace and norm lie in $ZZ$, the displayed factorization
    is a monic polynomial in $ZZ[T]$ having $alpha$ as a root. Thus $alpha$ is
    integral.
  ]
]

#block(breakable: false)[
  #theorem(title: "Ring of Integers of a Quadratic Field")[
    Let $d!=1$ be a squarefree integer and put $K=QQ(sqrt(d))$. Then

    $ cal(O)_K=cases(
      ZZ[(1+sqrt(d))\/2] quad & d equiv 1 mod 4,
      ZZ[sqrt(d)] quad & d equiv.not 1 mod 4
    ) $

    Equivalently, if

    $ omega=cases(
      (1+sqrt(d))\/2 quad & d equiv 1 mod 4,
      sqrt(d) quad & d equiv.not 1 mod 4
    ) $

    then ${1,omega}$ is an #emph[integral basis] of $K$ and
    $cal(O)_K=ZZ ⊕ ZZ omega$.
  ]
]

#proof[
  Let $alpha=a+b sqrt(d)$ with $a,b in QQ$. By the preceding lemma and the
  formulas from Chapter 2,

  $ "Tr"_(K slash QQ) (alpha)=2a, quad "N"_(K slash QQ) (alpha)=a^2-d b^2 $

  Suppose first that $alpha$ is integral. Set
  $m:=2a in ZZ$. The discriminant of its characteristic polynomial is

  $ m^2-4"N"_(K slash QQ) (alpha)=4d b^2 in ZZ $

  Write $b=u/v$ in lowest terms with $v>0$. The last integrality condition
  implies $v^2 divides 4d$. Since $d$ is squarefree, no odd prime can divide
  $v$, and $4$ cannot divide $v$. Hence $v divides 2$, so
  $n:=2b in ZZ$ and

  $ alpha=(m+n sqrt(d))\/2 $

  The norm is integral precisely when

  $ m^2-d n^2 equiv 0 mod 4 $

  If $d equiv 1 mod 4$, this says $m^2 equiv n^2 mod 4$. Since every square is
  congruent to $0$ or $1$ modulo $4$, the integers $m$ and $n$ have the same
  parity. Consequently,

  $ alpha=(m-n)\/2+n(1+sqrt(d))\/2 in ZZ[(1+sqrt(d))\/2] $

  If $d equiv.not 1 mod 4$, squarefreeness forces
  $d equiv 2 " or " 3 mod 4$. If $n$ were odd, then $d n^2$ would be
  congruent to $2$ or $3$ modulo $4$, neither of which is a square modulo
  $4$. Thus $n$ is even, and the same congruence then forces $m$ to be even.
  It follows that $alpha in ZZ[sqrt(d)]$. This proves the inclusion of
  $cal(O)_K$ in the displayed ring in both cases.

  For the reverse inclusion, $sqrt(d)$ is integral because it satisfies
  $T^2-d=0$. When $d equiv 1 mod 4$, the element
  $omega=(1+sqrt(d))\/2$ satisfies

  $ omega^2-omega+(1-d)\/4=0 $

  whose coefficients are integers. Thus $omega$ is integral. Since the
  algebraic integers form a ring, $ZZ[omega] subset.eq cal(O)_K$, completing
  the proof.
]

In particular,

$ cal(O)_(QQ(i))=ZZ[i], quad cal(O)_(QQ(sqrt(-5)))=ZZ[sqrt(-5)] $

so the two running examples from the previous chapters are genuinely rings
of integers and hence Dedekind domains.
