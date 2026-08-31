#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Extensions of Complete DVRs

Let $A$ be a complete DVR with fraction field $K$, maximal ideal
$frak(p)$, normalized valuation $v_(frak(p))$, and residue field
$k=A slash frak(p)$. Let $L slash K$ be a finite extension of degree $n$, and
let $B$ be the integral closure of $A$ in $L$.

The previous chapter supplied Hensel's lemma inside one complete field. We now
ask what happens when the field itself is enlarged. There are three basic
questions.

+ Does the absolute value on $K$ extend to $L$, and is $L$ still complete?

+ Can the integral closure $B$ be described by one generator?

+ Which part of $L slash K$ changes only the residue field, and which part
  changes the valuation?

When $L slash K$ is separable, the answers fit together particularly cleanly:
$B$ is a complete DVR with one maximal ideal $frak(q)$, and

$ [L:K]=e f $

where $e=e_(frak(q) slash frak(p))$ is the ramification index and
$f=[B slash frak(q):A slash frak(p)]$ is the residue degree.

#quote[
  A finite extension of a complete discretely valued field splits naturally
  into a residue-field extension and a totally ramified extension.
]

== Extending the Absolute Value

=== Norms on Finite-Dimensional Vector Spaces

We first separate two uses of the word norm. A vector-space norm measures the
size of vectors; the field norm $"N"_(L slash K)$ is the determinant of a
multiplication map. The second will soon produce the first.

#definition(title: "Norm on a Vector Space")[
  Let $(K,abs(dot))$ be an absolute-valued field and let $V$ be a
  $K$-vector space. A #emph[norm] on $V$ is a function

  $ norm(dot):V->RR_(>=0) $

  such that, for $v,w in V$ and $lambda in K$,

  + $norm(v)=0$ if and only if $v=0$;

  + $norm(lambda v)=abs(lambda)norm(v)$;

  + $norm(v+w)<=norm(v)+norm(w)$.

  It defines a translation-invariant metric

  $ d(v,w):=norm(v-w) $
]

#example(title: "The Supremum Norm")[
  Let $(e_1,dots,e_r)$ be a basis of $V$ and write

  $ v=sum_(i=1)^r v_i e_i $

  Then

  $ norm(v)_infinity:=max_(1<=i<=r) abs(v_i) $

  is a norm. If $V$ is a $K$-algebra and $abs(dot)_V$ is an absolute value on
  $V$, then $abs(dot)_V$ is a norm on the underlying $K$-vector space exactly
  when it extends the absolute value of $K$.
]

#theorem(title: "Equivalence of Norms in Finite Dimension")[
  Let $K$ be complete and let $V$ be finite-dimensional over $K$. Any two
  norms on $V$ induce the same topology, and this topology is complete.
  Equivalently, for any norm $norm(dot)$ and any basis there are constants
  $C_1,C_2>0$ such that

  $ C_1 norm(v)_infinity<=norm(v)<=C_2 norm(v)_infinity $
]

#proof[
  The upper bound follows immediately from the triangle inequality:

  $ norm(sum_i v_i e_i)<=sum_i abs(v_i)norm(e_i)<=C_2 norm(v)_infinity $

  with $C_2=sum_i norm(e_i)$.

  We prove the lower bound by induction on $r=dim_K V$. It is clear for
  $r=1$. Put $W="span"_K (e_1,dots,e_(r-1))$. By induction, $W$ is complete
  and hence closed in $V$. Since $e_r in.not W$,

  $ delta:=inf_(w in W) norm(e_r-w)>0 $

  Indeed, an infimum of zero would give a sequence in $W$ converging to
  $e_r$, contradicting closedness. If $v=w+a e_r$, then

  $ norm(v)>=abs(a)delta $

  so $abs(a)$ is bounded by a constant times $norm(v)$. The triangle
  inequality then bounds $norm(w)$, and the induction hypothesis bounds all
  coordinates of $w$. This gives $norm(v)_infinity<=C norm(v)$.

  Equivalent norms have the same Cauchy sequences. The sup-norm identifies
  $V$ topologically with $K^r$, which is complete because $K$ is complete.
]

#remark(title: "Why Finite Dimension Matters")[
  In infinite-dimensional analysis, inequivalent norms are common and
  completeness becomes an additional structure. Finite algebraic extensions
  are rigid: once the base field is complete, every reasonable way of
  measuring vectors produces the same topology.
]

=== The Unique Extension Theorem

Fix $0<c<1$ and normalize the absolute value of $K$ by

$ abs(x)_(frak(p)):=c^(v_(frak(p)) (x)) $

#theorem(title: "Extension of the Absolute Value to a Finite Extension")[
  Let $L slash K$ be a finite extension of degree $n$.

  + There is exactly one absolute value on $L$ extending
    $abs(dot)_(frak(p))$, namely

    $ abs(x)_L:=abs("N"_(L slash K) (x))_(frak(p))^(1/n) $

  + The field $L$ is complete for this absolute value, and

    $ B={x in L:abs(x)_L<=1} $

  + If $L slash K$ is separable, then $B$ is a complete DVR. If
    $frak(q)$ is its maximal ideal and
    $frak(p)B=frak(q)^e$, then

    $ abs(x)_L=c^(v_(frak(q)) (x)/e) $
]

#proof[
  Put

  $ rho(x):=abs("N"_(L slash K) (x))_(frak(p))^(1/n) $

  It is positive away from zero and multiplicative. For $x in K$,
  multiplication by $x$ on the $n$-dimensional space $L$ has determinant
  $x^n$, so

  $ rho(x)=abs(x^n)_(frak(p))^(1/n)=abs(x)_(frak(p)) $

  Thus $rho$ extends the absolute value of $K$, provided that it satisfies
  the triangle inequality.

  The norm criterion for integrality from the preceding chapter gives

  $ rho(x)<=1 <=> "N"_(L slash K) (x) in A <=> x in B $

  Since $B$ is a ring,

  $ rho(x)<=1 => x in B => x+1 in B => rho(x+1)<=1 $

  If $rho(y)<=rho(z)$ and $z!=0$, then $rho(y slash z)<=1$, hence

  $ rho(y+z)=rho(z)rho(y slash z+1)<=rho(z)=max(rho(y),rho(z)) $

  This is the ultrametric inequality, so $rho$ is an absolute value.

  Any absolute value on $L$ extending that of $K$ is a norm on the
  finite-dimensional $K$-vector space $L$. The norm-equivalence theorem says
  that it has the same topology as $rho$. Two nontrivial absolute values that
  define the same topology differ by a positive power; restriction to $K$
  forces that power to be $1$. This proves uniqueness. The same theorem also
  shows that $L$ is complete. Its closed unit ball is exactly $B$, so $B$ is
  complete as well.

  Now suppose $L slash K$ is separable. The integral closure of a complete DVR
  in a finite separable extension is a DVR; write its maximal ideal as
  $frak(q)$. Since

  $ v_(frak(q)) (x)=e v_(frak(p)) (x) quad "for " x in K^times $

  the absolute value $x mapsto c^(v_(frak(q)) (x)\/e)$ extends
  $abs(dot)_(frak(p))$. Uniqueness identifies it with $rho$.
]

#corollary(title: "Valuation of the Field Norm")[
  In the separable case, for every $x in L$,

  $ v_(frak(p)) ("N"_(L slash K) (x))=f v_(frak(q)) (x) $
]

#proof[
  The unique-extension formula gives

  $ c^(v_(frak(p)) ("N"_(L slash K) (x))\/n)=c^(v_(frak(q)) (x)\/e) $

  and $n=e f$. Comparing exponents proves the claim.
]

#remark(title: "Extension to an Algebraic Closure")[
  The transitivity of the field norm makes the formula compatible in finite
  towers. The absolute value therefore extends uniquely to an algebraic
  closure $overline(K)$.

  This is another face of Hensel's lemma: a valuation ring is henselian if
  and only if its valuation extends uniquely, up to the prescribed
  normalization, to every algebraic extension of its fraction field.
]

=== Normalized Valuations and Value Groups

The discrete valuation $v_(frak(q))$ does not literally restrict to
$v_(frak(p))$; it restricts to $e v_(frak(p))$. If one wants equality on the
base field, use the normalized extension

$ w_L:=1/e v_(frak(q)):L^times->1/e ZZ $

Then $w_L|_K=v_(frak(p))$. Passing through all finite subextensions of
$overline(K)$ produces a valuation with value group $QQ$.

#remark(title: "Discrete versus Compatible Normalization")[
  There are two useful conventions.

  + Keep integer-valued valuations on every finite extension. Then
    $v_(frak(q)) |_K=e v_(frak(p))$, and ramification is visible in the
    scaling factor.

  + Normalize all valuations to restrict to $v_(frak(p))$. Then the value
    group of $L$ is $1/e ZZ$, and ramification is visible in the new
    denominators.

  The absolute value $c^(w_L (dot))$ follows the second convention.
]

Recall also that a valuation ring can be defined without first naming a
valuation: an integral domain $R$ with fraction field $F$ is a valuation ring
if, for every $x in F^times$, either $x in R$ or $x^(-1) in R$. Conversely,
every valuation ring arises as

$ R={x in F:v(x)>=0} $

for a valuation with values in a totally ordered abelian group. Thus the
closed unit ball in the extension theorem is intrinsically a valuation ring.

== Local Dedekind--Kummer and Monogenicity

Globally, Dedekind--Kummer needs a monogenic order and may fail at primes
dividing its conductor. Locally over a complete DVR, separability of the
residue extension removes this obstruction: the entire integral closure has
one generator.

=== Nakayama's Lemma and a Local Factorization Rule

#lemma(title: "Nakayama's Lemma")[
  Let $(R,frak(m))$ be a local ring and let $M$ be a finitely generated
  $R$-module. If the images of $x_1,dots,x_s in M$ span
  $M slash frak(m)M$ over $R slash frak(m)$, then $x_1,dots,x_s$ generate
  $M$ over $R$.
]

#proof[
  Let $N=sum_i R x_i$ and $Q=M slash N$. The hypothesis says
  $Q=frak(m)Q$. Choose generators $q_1,dots,q_r$ of $Q$ and write

  $ q_i=sum_j a_(i j)q_j, quad a_(i j) in frak(m) $

  If $C=(a_(i j))$, then $(I-C)q=0$. Multiplying by the adjugate matrix shows
  that $"det"(I-C)$ annihilates every $q_i$. But
  $"det"(I-C) equiv 1 mod frak(m)$, so it is a unit. Hence every $q_i=0$,
  which means $Q=0$ and $M=N$.
]

#corollary(title: "Maximal Ideals Lie over the Closed Point")[
  Let $(R,frak(m))$ be noetherian local, let $g in R[X]$ be monic, and put

  $ C:=R[X] slash (g) $

  Every maximal ideal of $C$ contains $frak(m)C$.
]

#proof[
  If a maximal ideal $frak(n)$ did not contain $frak(m)C$, then
  $frak(n)+frak(m)C=C$. The algebra $C$ is finite over $R$ because $g$ is
  monic, so the ideal $frak(n)$ is a finitely generated $R$-module. Its
  generators would span $C slash frak(m)C$, and Nakayama's lemma would imply
  $frak(n)=C$, a contradiction.
]

#remark(title: "Why Monic Is Necessary")[
  The finiteness assumption matters. Without a monic polynomial,
  $R[X] slash (g)$ need not be finite over $R$, and maximal ideals need not
  lie over $frak(m)$. For example,
  $ZZ_((p))[X] slash (p X-1) tilde.eq QQ$ has a maximal ideal whose contraction
  does not contain $(p)$.
]

#corollary(title: [Local Dedekind--Kummer])[
  Let $(R,frak(m),k)$ be a noetherian local ring, let $g in R[X]$ be monic,
  and put

  $ C=R[X] slash (g)=R[alpha] $

  Factor the reduction into distinct monic irreducible factors

  $ overline(g)=product_(i=1)^r overline(g)_i^(a_i) $

  and choose monic lifts $g_i in R[X]$. Then the maximal ideals of $C$ are
  precisely

  $ frak(n)_i=(frak(m),g_i (alpha)), quad 1<=i<=r $
]

#proof[
  Every maximal ideal contains $frak(m)C$, so reduction gives a bijection

  $ {"maximal ideals of " C} tilde.eq {"maximal ideals of " C slash frak(m)C} $

  But

  $ C slash frak(m)C tilde.eq k[X] slash (overline(g)) $

  and the maximal ideals of this quotient correspond exactly to the distinct
  irreducible divisors $overline(g)_i$.
]

=== The Local Monogenicity Theorem

#theorem(title: "Integral Closure over a Complete DVR Is Locally Monogenic")[
  Assume that $L slash K$ is finite separable, let $B$ be the integral closure
  of $A$ in $L$, and put

  $ l:=B slash frak(q) $

  If $l slash k$ is separable, then

  $ B=A[alpha] $

  for some $alpha in B$. If $L slash K$ is unramified, this holds for every
  lift $alpha in B$ of every primitive element
  $overline(alpha) in l$ satisfying $l=k(overline(alpha))$.
]

#proof[
  Put

  $ frak(p)B=frak(q)^e, quad f=[l:k], quad n=[L:K]=e f $

  Since $l slash k$ is finite separable, choose
  $overline(alpha)_0 in l$ with
  $l=k(overline(alpha)_0)$. Let $overline(g) in k[X]$ be its monic minimal
  polynomial, choose a monic lift $g in A[X]$, and lift
  $overline(alpha)_0$ to $alpha_0 in B$.

  The element $g(alpha_0)$ lies in $frak(q)$. If its
  $frak(q)$-valuation is already $1$, put $alpha=alpha_0$. Otherwise choose a
  uniformizer $pi_0$ of $B$ and put

  $ alpha:=alpha_0+pi_0 $

  Taylor expansion gives

  $ g(alpha)=g(alpha_0)+pi_0 g'(alpha_0)+pi_0^2 h(alpha_0) $

  for some $h in B[X]$. Separability of $overline(g)$ implies that
  $g'(alpha_0)$ is a unit. The middle term has valuation $1$, while the other
  two terms have valuation at least $2$. Therefore

  $ pi:=g(alpha) $

  is a uniformizer of $B$.

  We claim that $1,alpha,dots,alpha^(n-1)$ span
  $B slash frak(p)B=B slash (pi^e)$ over $k$. Every residue class modulo
  $pi^e$ can be written

  $ b_0+b_1 pi+dots+b_(e-1)pi^(e-1) $

  where each $b_j$ is determined modulo $pi$. Since
  $1,overline(alpha),dots,overline(alpha)^(f-1)$ is a $k$-basis of
  $B slash (pi)=l$, each $b_j$ may be replaced modulo $pi$ by a polynomial in
  $alpha$ of degree at most $f-1$. Substituting $pi=g(alpha)$, whose degree is
  $f$, produces a polynomial in $alpha$ of degree at most

  $ (f-1)+f(e-1)=e f-1=n-1 $

  Thus the powers through $alpha^(n-1)$ span $B slash frak(p)B$. Nakayama's
  lemma now shows that they span $B$ over $A$, so $B=A[alpha]$.

  If the extension is unramified, then $e=1$ and $f=n$. The first
  $n$ powers of any lift of a residue-field generator already span
  $B slash frak(p)B=l$, so Nakayama applies without modifying the lift.
]

#remark(title: "Arithmetic and Geometric Meaning")[
  The residue generator supplies the horizontal directions in the closed
  fiber, while the uniformizer supplies its infinitesimal thickness. The
  element $alpha$ is chosen so that the single polynomial $g(alpha)$ records
  the vertical parameter. Consequently the powers of $alpha$ encode both
  pieces at once.

  Geometrically, the finite local map $Spec B->Spec A$ has one closed point.
  Separability makes the reduced closed fiber simple enough that one
  coordinate, corrected in the ramified direction, generates its entire
  infinitesimal neighborhood.
]

The theorem lets local Dedekind--Kummer operate without a conductor
condition. It also prepares the basic decomposition of a finite extension
into the two extreme cases:

+ #emph[unramified], where $e=1$ and the degree is entirely visible in the
  residue field;

+ #emph[totally ramified], where $f=1$ and the degree is entirely visible in
  the value group.

== Unramified Extensions and Residue Fields

=== The Equivalence of Categories

#definition(title: "The Two Categories")[
  Let $"Unr"_K$ be the category whose objects are finite unramified field
  extensions of $K$ and whose morphisms are $K$-algebra homomorphisms.

  Let $"Sep"_k$ be the category whose objects are finite separable field
  extensions of $k$ and whose morphisms are $k$-algebra homomorphisms.
]

If $L_i slash K$ is unramified, write $B_i$ for its valuation ring,
$frak(q)_i$ for the maximal ideal, and
$l_i=B_i slash frak(q)_i$ for the residue field. A $K$-embedding
$phi:L_1->L_2$ preserves the unique extended absolute value, hence maps
$B_1$ into $B_2$ and $frak(q)_1$ into $frak(q)_2$. It therefore induces

$ overline(phi):l_1->l_2 $

#theorem(title: "Unramified Extensions Are the Same as Separable Residue Extensions")[
  Reduction defines an equivalence of categories

  $ F:"Unr"_K tilde.eq "Sep"_k, quad L mapsto l $

  In particular, it induces a bijection on isomorphism classes and, for
  finite unramified extensions $L_1,L_2 slash K$, a bijection

  $ Hom_K (L_1,L_2) tilde.eq Hom_k (l_1,l_2) $
]

#proof[
  We first prove essential surjectivity. Let $l slash k$ be finite separable.
  Choose a primitive element and write

  $ l tilde.eq k[X] slash (overline(g)) $

  with $overline(g)$ monic, irreducible, and separable. Lift it to a monic
  $g in A[X]$. The irreducibility criterion from the preceding chapter shows
  that $g$ is irreducible over $K$. Its discriminant is a unit, so

  $ C:=A[X] slash (g) $

  is finite étale over $A$. Its closed fiber is the field $l$, so $C$ is
  local; a finite étale local algebra over a DVR is again a DVR. Its fraction
  field

  $ L:=K[X] slash (g) $

  has degree $[l:k]$, ramification index $1$, and residue field $l$. Hence
  $L slash K$ is unramified and $F(L) tilde.eq l$.

  We next prove full faithfulness. Let $L_1 slash K$ be unramified. By local
  monogenicity, choose $alpha in B_1$ such that

  $ B_1=A[alpha], quad l_1=k(overline(alpha)) $

  and let $g in A[X]$ be the minimal polynomial of $alpha$. A
  $K$-homomorphism $L_1->L_2$ is determined by a root of $g$ in $L_2$.
  Since $g$ is monic, every such root lies in $B_2$. Likewise, a
  $k$-homomorphism $l_1->l_2$ is determined by a root of $overline(g)$ in
  $l_2$. The polynomial $overline(g)$ is separable, so Hensel's lemma gives a
  bijection

  $ {"roots of " g " in " B_2} tilde.eq {"roots of " overline(g) " in " l_2} $

  This is exactly the map on Hom-sets induced by reduction.
]

#remark(title: "A Connected Form of the Henselian Equivalence")[
  The preceding chapter proved

  $ "FinEt"(A) tilde.eq "FinEt"(k) $

  for every henselian local ring $A$. Finite étale algebras correspond to
  finite étale covers, and their connected objects are precisely unramified
  field extensions on the generic side and finite separable field extensions
  on the residue side. The equivalence
  $"Unr"_K tilde.eq "Sep"_k$ is therefore the connected, field-valued shadow of
  that geometric theorem.
]

#remark(title: "The Target May Be Ramified")[
  In the full-faithfulness argument, only $L_1 slash K$ needed to be
  unramified. For any finite extension $L_2 slash K$ whose valuation ring is
  henselian, reduction still gives

  $ Hom_K (L_1,L_2) tilde.eq Hom_k (l_1,l_2) $

  whenever the residue fields are interpreted using the chosen valuation.
]

#corollary(title: "Polynomial Characterization of Unramified Extensions")[
  The finite separable extension $L slash K$ is unramified if and only if

  $ B=A[alpha] $

  for some $alpha in B$ whose minimal polynomial $g in A[X]$ has separable
  reduction $overline(g) in k[X]$.
]

#proof[
  For an unramified extension, lift a primitive element of the separable
  residue extension and apply local monogenicity. Its minimal polynomial
  reduces to the separable minimal polynomial of the residue generator.

  Conversely, suppose $B=A[alpha]$ and $overline(g)$ is separable. If
  $overline(g)$ were reducible, Hensel factorization would give a nontrivial
  factorization of the minimal polynomial $g$ over $A$, hence over $K$.
  Thus $overline(g)$ is irreducible. It follows that

  $ B slash frak(p)B tilde.eq k[X] slash (overline(g)) $

  is a field of degree $deg(g)=[L:K]$. Therefore $frak(p)B$ is the maximal
  ideal, the residue degree equals $[L:K]$, and $e=1$.
]

=== Roots of Unity and Finite Residue Fields

#corollary(title: "Prime-to-Residue-Characteristic Roots of Unity")[
  Let $zeta_m$ be a primitive $m$th root of unity in $overline(K)$. If $m$ is
  prime to $"char"(k)$, then

  $ K(zeta_m) slash K $

  is unramified.
]

#proof[
  The derivative of $X^m-1$ is $m X^(m-1)$, which is invertible at every root
  modulo $frak(p)$. Thus $A[X] slash (X^m-1)$ is finite étale. Each connected
  factor of its generic fiber is therefore an unramified field extension, and
  $K(zeta_m)$ is one of these factors.
]

#theorem(title: "Classification over a Finite Residue Field")[
  Suppose $k=FF_q$. For every $n>=1$, there is, up to $K$-isomorphism, exactly
  one unramified extension of $K$ of degree $n$. It is

  $ K_n=K(zeta_(q^n-1)) $

  Its valuation ring is $A[zeta_(q^n-1)]$, its residue field is
  $FF_(q^n)$, and

  $ "Gal"(K_n slash K) tilde.eq "Gal"(FF_(q^n) slash FF_q) tilde.eq ZZ slash n ZZ $
]

#proof[
  The finite field $FF_q$ has exactly one degree-$n$ extension inside a fixed
  algebraic closure, namely $FF_(q^n)$. The categorical equivalence therefore
  gives a unique unramified degree-$n$ extension of $K$.

  The cyclic group $FF_(q^n)^times$ has order $q^n-1$. Choose a generator
  $overline(alpha)$. Its Teichmüller lift is a primitive
  $(q^n-1)$st root of unity, and local monogenicity shows that it generates
  both the field and its valuation ring. Hence the extension is
  $K(zeta_(q^n-1))$.

  Finally, the equivalence identifies automorphisms of the field with
  automorphisms of the residue field. The latter group is cyclic of order
  $n$, generated by $x mapsto x^q$.
]

#example(title: [The Unramified Extensions of $QQ_p$])[
  For every $n>=1$, the field $QQ_p$ has one unramified extension of degree
  $n$ up to $QQ_p$-isomorphism:

  $ QQ_p (zeta_(p^n-1)) $

  Its residue field is $FF_(p^n)$. The minimal polynomial of a suitable
  primitive $(p^n-1)$st root of unity has degree $n$ and divides

  $ X^(p^n-1)-1 $
]

#corollary(title: [Cyclotomic Ramification over an Unramified $p$-adic Base])[
  Let $p$ be odd, let $K slash QQ_p$ be finite unramified, and let $m>=1$.
  Then

  $ K(zeta_m) slash K " is ramified" <=> p divides m $
]

#proof[
  If $p$ does not divide $m$, the extension is unramified by the
  prime-to-residue-characteristic result.

  If $p$ divides $m$, the extension contains $K(zeta_p)$. The extension
  $QQ_p (zeta_p) slash QQ_p$ is a nontrivial totally ramified extension, and
  an unramified extension of $QQ_p$ is linearly disjoint from it. Therefore
  $K(zeta_p) slash K$ is nontrivial and totally ramified, so
  $K(zeta_m) slash K$ is ramified.
]

#remark(title: "Why the Base-Field Hypothesis Is Needed")[
  For an arbitrary ramified $p$-adic field, the condition
  $zeta_p in.not K$ alone is not sufficient. For example, let

  $ K=QQ_3 (sqrt(3)) $

  Then $zeta_3 in.not K$, but

  $ K(zeta_3)=K(sqrt(-1)) $

  is the unramified quadratic extension of $K$. Thus the commonly quoted
  cyclotomic criterion must retain a hypothesis controlling the ramification
  already present in the base field.
]

=== Norms of Units

#theorem(title: "Unit Norms in an Unramified Extension")[
  Suppose that $k$ is finite. If $L slash K$ is unramified, then

  $ "N"_(L slash K) (B^times)=A^times $

  Conversely, if $L slash K$ is finite, tamely ramified, and abelian, then
  surjectivity of this norm map implies that $L slash K$ is unramified.
]

#proof[
  Assume first that $L slash K$ is unramified. Then
  $frak(p)B=frak(q)$, and the residue-field norm

  $ "N"_(l slash k):l^times->k^times $

  is surjective because both groups are cyclic. Given $u in A^times$, choose
  $b_0 in B^times$ whose residue norm agrees with $overline(u)$. Then

  $ "N"_(L slash K) (b_0) equiv u mod frak(p) $

  For $r>=1$, the norm on successive principal-unit quotients is governed by
  the residue trace:

  $ "N"_(L slash K) (1+pi^r y) equiv 1+pi^r "Tr"_(l slash k) (overline(y)) mod pi^(r+1) $

  where $pi$ is a uniformizer of $A$ and also of $B$. The trace
  $l->k$ is surjective, so we may successively multiply $b_0$ by principal
  units to correct its norm modulo
  $frak(p)^2,frak(p)^3,dots$. Completeness makes the product converge to a
  $b in B^times$ satisfying $"N"_(L slash K) (b)=u$.

  For the converse, let $E$ be the maximal unramified subextension introduced
  below. Then $L slash E$ is totally ramified of degree $e$. Because
  $L slash K$ is tame, its inertia group is cyclic of order $e$. Frobenius
  conjugates tame inertia by the $|k|$th-power map; abelianity makes this
  action trivial, so $e$ divides $|k^times|$. On residue units, the norm from
  the totally ramified part is the $e$th-power map. Its image, and hence the
  residue of every norm from $L$, lies in $(k^times)^e$. If $e>1$, this is a
  proper subgroup, so the unit norm cannot be surjective. Hence $e=1$ and the
  extension is unramified.
]

#remark(title: "The Converse Is False without Extra Hypotheses")[
  Take $K=QQ_5$ and $L=QQ_5 (root(3,5))$. This is a totally ramified,
  non-Galois cubic extension. The cube map is an automorphism of
  $ZZ_5^times$, because $3$ is coprime to both $5$ and $|FF_5^times|=4$.
  Every $u in ZZ_5^times$ is therefore $x^3$ for some
  $x in ZZ_5^times$, and

  $ u=x^3="N"_(L slash K) (x) $

  Thus the norm on units is surjective although the extension is ramified.
]

== Maximal Unramified Subextensions

=== The Maximal Unramified Extension

#definition(title: "Maximal Unramified Extension")[
  Let $Omega slash K$ be a separable algebraic extension. The
  #emph[maximal unramified extension of $K$ inside $Omega$] is the union

  $ Omega^"unr":=union_(K subset.eq E subset.eq Omega, E slash K " finite unramified") E $

  When $Omega=K^"sep"$, it is denoted $K^"unr"$.
]

#example(title: [The Field $QQ_p^"unr"$])[
  Reduction identifies the Galois group of the maximal unramified extension
  with the absolute Galois group of the residue field:

  $ "Gal"(QQ_p^"unr" slash QQ_p) tilde.eq "Gal"(overline(FF_p) slash FF_p) $

  Since every finite extension of $FF_p$ is $FF_(p^n)$,

  $ "Gal"(QQ_p^"unr" slash QQ_p) tilde.eq varprojlim(n) ZZ slash n ZZ=:hat(ZZ) $

  where the transition system is ordered by divisibility. The group
  $hat(ZZ)$ is the profinite completion of $ZZ$ and is topologically generated
  by Frobenius.

  The field $QQ_p^"unr"$ has value group $ZZ$ and residue field
  $overline(FF_p)$. It is not complete: completing it produces a strictly
  larger field with the same value group and residue field.
]

=== The Unramified--Totally Ramified Decomposition

#theorem(title: "Canonical Decomposition of a Finite Extension")[
  Let $L slash K$ be finite separable, and suppose its residue extension
  $l slash k$ is separable. Let $e$ and $f$ be its ramification index and
  residue degree. There is a unique intermediate field $E$ such that

  + $E slash K$ is unramified of degree $f$ and contains every unramified
    subextension of $L slash K$;

  + $L slash E$ is totally ramified of degree $e$.

  If $L slash K$ is Galois, then, for the unique maximal ideal $frak(q)$ of
  $B$,

  $ D_(frak(q))="Gal"(L slash K) $

  $ I_(frak(q))="Gal"(L slash E) $

  and $E slash K$ is Galois with

  $ "Gal"(E slash K) tilde.eq D_(frak(q)) slash I_(frak(q)) tilde.eq "Gal"(l slash k) $
]

#proof[
  The separable residue extension $l slash k$ corresponds under
  $"Unr"_K tilde.eq "Sep"_k$ to an unramified extension $E slash K$ of degree
  $f$. The identity embedding $l->l$ lifts uniquely to a $K$-embedding
  $E->L$, so we may regard $E$ as a subfield of $L$.

  If $F slash K$ is any unramified subextension of $L slash K$, its residue
  field is a separable subextension of $l slash k$. The inclusion of residue
  fields lifts uniquely, by full faithfulness, to an embedding $F->E$
  compatible with their embeddings in $L$. Hence $F subset.eq E$, proving
  maximality and uniqueness.

  Since $[E:K]=f$,

  $ [L:E]=[L:K]/[E:K]=e f/f=e $

  The fields $E$ and $L$ have the same residue field $l$, so the residue
  degree of $L slash E$ is $1$. Its entire degree is therefore ramification,
  and $L slash E$ is totally ramified.

  Now suppose $L slash K$ is Galois. Completeness gives a unique extension of
  the valuation, so every element of $"Gal"(L slash K)$ fixes
  $frak(q)$. Thus the decomposition group is the whole Galois group. The
  reduction map gives the exact sequence

  $ 1->I_(frak(q))->D_(frak(q))->"Gal"(l slash k)->1 $

  The inertia group has order $e$, while
  $"Gal"(L slash E)$ also has order $e$. Both act trivially on $l$, so they
  coincide. Since inertia is normal, its fixed field $E$ is Galois over $K$,
  and the quotient identifies with $"Gal"(l slash k)$.
]

#remark(title: "The Geometric Picture")[
  The finite map $Spec B->Spec A$ has a single closed point. The intermediate
  scheme $Spec cal(O)_E$ separates its two kinds of local information:

  $ Spec B -> Spec cal(O)_E -> Spec A $

  The second map is finite étale and enlarges the closed point from
  $Spec k$ to $Spec l$. The first map leaves the closed point unchanged but
  thickens the valuation direction by the ramification index $e$.
]

#block(breakable: false)[
  #align(center, table(
    columns: (1.15fr, 1fr, 1fr, 1.65fr),
    align: (center, center, center, center),
    inset: (x: 9pt, y: 5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[Extension]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Degree]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Residue field]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[What changes]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    [$E slash K$], [$f$], [$l slash k$], [closed point],
    [$L slash E$], [$e$], [trivial], [value group and thickness],
    [$L slash K$], [$e f$], [$l slash k$], [both pieces],
  ))
]

#quote[
  Unramified extensions move along the closed fiber; totally ramified
  extensions move in the valuation direction.
]

== Totally Ramified Extensions

Let $A$ be a complete DVR with fraction field $K$, maximal ideal
$frak(p)$, and residue field $k$. For a finite separable extension
$L slash K$, let $B$ be the integral closure of $A$ in $L$. The preceding
sections showed that $B$ is a complete DVR with a unique maximal ideal
$frak(q)$, and that

$ [L:K]=e_(L slash K) f_(L slash K) $

It also isolated the maximal unramified subextension. We now turn to the
opposite extreme: a #emph[totally ramified] extension has

$ e_(L slash K)=[L:K], quad f_(L slash K)=1 $

so the residue field does not change and the entire degree is recorded by the
value group. Eisenstein polynomials are the natural equations for precisely
this phenomenon.

#quote[
  An unramified extension enlarges the residue field; an Eisenstein equation
  cuts the valuation step into smaller pieces.
]

== Eisenstein Polynomials

=== The Classical Criterion over $ZZ$

We begin with the familiar global statement. It is easy to apply, but its
real explanation is local and valuation-theoretic.

#definition(title: "Eisenstein at a Rational Prime")[
  Let

  $ f(X)=a_n X^n+a_(n-1)X^(n-1)+dots+a_1 X+a_0 in ZZ[X] $

  with $n>=1$. For a prime number $p$, the polynomial $f$ is
  #emph[Eisenstein at $p$] if

  $ p divides.not a_n $

  $ p divides a_i quad "for every " 0<=i<n $

  $ p^2 divides.not a_0 $
]

#theorem(title: "Classical Eisenstein Criterion")[
  If $f in ZZ[X]$ is Eisenstein at a prime $p$, then $f$ is irreducible in
  $QQ[X]$.
]

#proof[
  Dividing by the content does not affect irreducibility over $QQ$, so Gauss's
  lemma lets us work with a primitive polynomial in $ZZ[X]$. Suppose that

  $ f=g h $

  with $g,h in ZZ[X]$ of positive degree. Reduction modulo $p$ gives

  $ overline(f)=overline(a)_n X^n $

  Since $FF_p[X]$ is a domain and $overline(a)_n!=0$, both
  $overline(g)$ and $overline(h)$ must be nonzero monomials. Because both
  factors have positive degree, their constant coefficients are divisible by
  $p$. Their product $a_0$ is then divisible by $p^2$, contradicting the
  Eisenstein hypothesis.
]

#example(title: "The Basic Family")[
  For every prime $p$ and every $n>=1$,

  $ X^n-p $

  is Eisenstein at $p$. Hence it is irreducible over $QQ$, and
  $[QQ(root(n,p)):QQ]=n$.
]

#example(title: "A Shift Can Reveal Eisenstein Behavior")[
  The polynomial $X^4+1$ is not Eisenstein in its displayed form, but the
  invertible change of variable $X mapsto X+1$ gives

  $ (X+1)^4+1=X^4+4X^3+6X^2+4X+2 $

  which is Eisenstein at $2$. Therefore $X^4+1$ is irreducible over $QQ$.

  More generally,

  $ Phi_p (X+1)=((X+1)^p-1)/X $

  is Eisenstein at $p$, giving the usual proof that the $p$th cyclotomic
  polynomial $Phi_p$ is irreducible.
]

#remark(title: "A Sufficient, Not Necessary, Criterion")[
  Eisenstein's criterion does not classify all irreducible polynomials.
  For example, many irreducible polynomials have unit constant term at every
  prime and therefore cannot be Eisenstein. Its strength is that a small
  amount of divisibility data forces irreducibility immediately.
]

=== Eisenstein Polynomials over a DVR

Let $A$ now be an arbitrary DVR with maximal ideal
$frak(p)=(pi_A)$, normalized valuation $v_(frak(p))$, and fraction field
$K$. The uniformizer $pi_A$ replaces the rational prime $p$.

#definition(title: "Eisenstein Polynomial of a DVR")[
  A monic polynomial

  $ f(X)=X^n+a_(n-1)X^(n-1)+dots+a_1 X+a_0 in A[X] $

  is #emph[Eisenstein] if

  $ a_i in frak(p) quad "for every " 0<=i<n $

  $ a_0 in.not frak(p)^2 $

  Equivalently,

  $ v_(frak(p)) (a_i)>=1 quad "for " 0<=i<n, quad v_(frak(p)) (a_0)=1 $

  Thus the constant coefficient is a uniformizer up to multiplication by a
  unit.
]

#remark(title: "What the Reduction Remembers")[
  Modulo the maximal ideal, every degree-$n$ Eisenstein polynomial becomes

  $ overline(f)=X^n $

  so the closed fiber has just one point, with multiplicity $n$. The extra
  condition $a_0 in.not frak(p)^2$ says that this multiplicity comes from one
  genuine valuation step rather than from a polynomial that was already
  divisible too deeply.
]

#theorem(title: "Eisenstein Irreducibility over a DVR")[
  Let $A$ be a DVR with fraction field $K$. Every Eisenstein polynomial
  $f in A[X]$ is irreducible in both $A[X]$ and $K[X]$.
]

#proof[
  Suppose that $f=g h$ in $K[X]$, with $g$ and $h$ monic of positive degree.
  Since $f$ is monic, every coefficient of $g$ and $h$ is integral over $A$.
  A DVR is integrally closed, so in fact $g,h in A[X]$.

  Reduction modulo $frak(p)$ gives

  $ X^n=overline(g)overline(h) $

  Both factors are monic, hence

  $ overline(g)=X^r, quad overline(h)=X^(n-r) $

  for some $0<r<n$. Their constant coefficients both lie in $frak(p)$, so
  their product $a_0$ lies in $frak(p)^2$, contradicting
  $v_(frak(p)) (a_0)=1$. Thus $f$ is irreducible over $K$, and therefore also
  over $A$.
]

#corollary(title: "Eisenstein at a Prime of a Dedekind Domain")[
  Let $R$ be a Dedekind domain with fraction field $F$, let
  $frak(p)$ be a nonzero prime ideal, and let

  $ f(X)=X^n+a_(n-1)X^(n-1)+dots+a_0 in R[X] $

  Suppose

  $ a_i in frak(p) quad "for " 0<=i<n, quad a_0 in.not frak(p)^2 $

  Then $f$ is irreducible over $F$.
]

#proof[
  The localization $R_(frak(p))$ is a DVR with fraction field $F$, and the
  displayed conditions say exactly that $f$ is Eisenstein over
  $R_(frak(p))$. Apply the DVR criterion.
]

#remark(title: "Why Localization Is the Right Generalization")[
  The classical test only uses divisibility at one prime. Passing from
  $R$ to $R_(frak(p))$ discards every other prime and turns the chosen prime
  into a uniformizer. Eisenstein's criterion is therefore intrinsically a
  local statement, even when it is first encountered over $ZZ$.
]

=== An Eisenstein Root Produces a DVR

Irreducibility is only the first consequence. The quotient by an Eisenstein
polynomial already carries the valuation ring of a totally ramified field.

#theorem(title: "The Eisenstein Quotient Is a DVR")[
  Let $A$ be a DVR and let $f in A[X]$ be Eisenstein of degree $n$. Put

  $ C:=A[X] slash (f)=A[pi] $

  where $pi$ is the image of $X$. Then $C$ is a DVR with uniformizer $pi$.
  Its fraction field has degree $n$ over $K$, its residue field is
  $A slash frak(p)$, and

  $ frak(p)C=(pi)^n $
]

#proof[
  Eisenstein irreducibility embeds $C$ into the field
  $K[X] slash (f)$, so $C$ is a domain. Since

  $ C slash frak(p)C tilde.eq k[X] slash (X^n) $

  the local Dedekind--Kummer result shows that $C$ has a unique maximal ideal

  $ frak(q)=(frak(p),pi) $

  Write

  $ f(X)=X^n+a_(n-1)X^(n-1)+dots+a_1 X+a_0 $

  The constant coefficient $a_0$ generates $frak(p)$, and the relation
  $f(pi)=0$ gives

  $ a_0=-pi(a_1+a_2 pi+dots+a_(n-1)pi^(n-2)+pi^(n-1)) $

  Hence $frak(p)C subset.eq (pi)$ and
  $frak(q)=(frak(p),pi)=(pi)$. The ring $C$ is a one-dimensional noetherian
  local domain whose nonzero maximal ideal is principal, so it is a DVR with
  uniformizer $pi$.

  Since a DVR is integrally closed, $C$ is already the integral closure of
  $A$ in its fraction field: every element integral over $A$ is also integral
  over $C$ and hence lies in $C$. Its residue field is $k$, and it is free of
  rank $n$ over $A$ with basis $1,pi,dots,pi^(n-1)$. The fundamental identity
  therefore gives

  $ n=e_(C slash A) f_(C slash A)=e_(C slash A) $

  so $frak(p)C=(pi)^n$.
]

#corollary(title: "Every Eisenstein Polynomial Defines a Totally Ramified Extension")[
  If $f in A[X]$ is Eisenstein of degree $n$ and

  $ L:=K[X] slash (f) $

  then $L slash K$ is totally ramified of degree $n$. Its valuation ring is
  $A[pi]$, and $pi$ is a uniformizer.
]

#proof[
  The preceding theorem shows that $A[pi]$ is a DVR with fraction field $L$.
  In particular it is integrally closed, so it is the integral closure of
  $A$ in $L$. The equality $frak(p)A[pi]=(pi)^n$ gives ramification index
  $n$ and residue degree $1$.
]

#quote[
  Eisenstein does more than prove irreducibility: it writes down the
  valuation ring and its uniformizer at the same time.
]

=== Characterizing Totally Ramified Extensions

The converse uses completeness through the fact that the integral closure is
a single complete DVR.

#theorem(title: "Uniformizers Characterize Total Ramification")[
  Let $A$ be a complete DVR, let $L slash K$ be finite separable of degree
  $n$, and let $B$ be the integral closure of $A$ in $L$. For a uniformizer
  $pi$ of $B$, the following are equivalent.

  + The extension $L slash K$ is totally ramified.

  + One has $B=A[pi]$, and the minimal polynomial of $pi$ over $K$ is
    Eisenstein over $A$.

  Consequently, in a totally ramified extension #emph[every] uniformizer of
  $B$ is a primitive element and has Eisenstein minimal polynomial.
]

#proof[
  First suppose that $B=A[pi]$ and the minimal polynomial of $pi$ is
  Eisenstein. The Eisenstein quotient theorem gives

  $ frak(p)B=(pi)^n=frak(q)^n $

  so the ramification index is $n=[L:K]$.

  Conversely, suppose $L slash K$ is totally ramified. Then

  $ v_(frak(q)) (K^times)=n ZZ $

  We claim that $1,pi,dots,pi^(n-1)$ are linearly independent over $K$.
  Indeed, for nonzero $c_i in K$ the valuations

  $ v_(frak(q)) (c_i pi^i)=n v_(frak(p)) (c_i)+i $

  are distinct modulo $n$. A nontrivial sum of these terms has a unique term
  of smallest valuation and therefore cannot vanish. Since $[L:K]=n$, these
  powers form a basis and $L=K(pi)$.

  Write the minimal polynomial as

  $ f(X)=X^n+a_(n-1)X^(n-1)+dots+a_1 X+a_0 $

  The element $pi$ is integral, and $A$ is integrally closed, so
  $f in A[X]$. In the relation

  $ pi^n+a_(n-1)pi^(n-1)+dots+a_1 pi+a_0=0 $

  the leading term has $frak(q)$-valuation $n$. For cancellation, the minimum
  valuation must occur at least twice. The terms
  $a_i pi^i$ for $1<=i<n$ have valuation congruent to $i$ modulo $n$, while
  the constant and leading terms have valuation congruent to zero. It follows
  that

  $ v_(frak(q)) (a_0)=n, quad v_(frak(q)) (a_i)>=n quad "for " 1<=i<n $

  Since $v_(frak(q)) |_K=n v_(frak(p))$, we obtain

  $ v_(frak(p)) (a_0)=1, quad v_(frak(p)) (a_i)>=1 $

  Thus $f$ is Eisenstein. The ring $A[pi]$ is therefore a DVR with fraction
  field $L$. Every element of $B$ is integral over $A[pi]$, and $A[pi]$ is
  integrally closed, so $B=A[pi]$.
]

#remark(title: "The Meaning of the Power Basis")[
  In an unramified extension, a lift of a residue-field generator gives a
  power basis. In a totally ramified extension, a uniformizer gives the power
  basis

  $ 1,pi,dots,pi^(n-1) $

  The two constructions are complementary: one generates through distinct
  residue classes, the other through distinct valuation classes modulo
  $n ZZ$.
]

=== A Newton-Polygon Generalization

Eisenstein corresponds to the simplest possible Newton polygon. This viewpoint
also detects irreducibility when the constant coefficient has valuation
greater than one.

#definition(title: "Newton Polygon")[
  Let

  $ f(X)=sum_(i=0)^n a_i X^i in K[X], quad a_0 a_n!=0 $

  The #emph[Newton polygon] $"NP"_(frak(p)) (f)$ is the lower convex hull in
  $RR^2$ of the points

  $ (i,v_(frak(p)) (a_i)), quad 0<=i<=n $

  Terms with $a_i=0$ are regarded as having infinite height and do not affect
  the lower hull.
]

For a monic Eisenstein polynomial, every intermediate point lies above the
line joining $(0,1)$ to $(n,0)$. Its Newton polygon is therefore a single
segment of slope $-1/n$.

#theorem(title: [Eisenstein--Dumas Criterion])[
  Let $A$ be a DVR and let

  $ f(X)=X^n+a_(n-1)X^(n-1)+dots+a_0 in A[X] $

  Suppose $v_(frak(p)) (a_0)=r>0$, with $gcd(n,r)=1$, and

  $ v_(frak(p)) (a_i)>=r(n-i)/n quad "for every " 0<i<n $

  Then $f$ is irreducible over $K$.
]

#proofsketch[
  The hypotheses say that the Newton polygon consists of the single segment
  from $(0,r)$ to $(n,0)$, of slope $-r/n$. Under multiplication, the slopes
  of Newton polygons combine with their horizontal lengths. If
  $f=g h$ with $g$ monic of degree $d$, then the polygon of $g$ can only use
  the slope $-r/n$. Its total vertical change is therefore $d r/n$, which
  must be an integer because the endpoints of a Newton polygon have integral
  coordinates. Since $gcd(n,r)=1$, this forces $n$ to divide $d$. No proper
  factor can have such a degree, so $f$ is irreducible.
]

#example(title: "Beyond the Basic Eisenstein Criterion")[
  For a uniformizer $pi_A$ and positive integers $n,r$ with
  $gcd(n,r)=1$,

  $ X^n-pi_A^r $

  is irreducible over $K$. When $r>1$, it is not Eisenstein in the basic
  sense, but its one-segment Newton polygon still forces irreducibility.
]

#remark(title: "Why Coprimality Appears")[
  The fraction $r/n$ is the valuation of every root predicted by the unique
  Newton slope. If $r$ and $n$ have a common divisor, this denominator becomes
  smaller and a proper factor may carry an integral portion of the segment.
  For an ordinary Eisenstein polynomial $r=1$, coprimality is automatic.
]

== Tame and Wild Ramification

Let $L slash K$ be a finite separable extension as in the beginning of the
chapter, and assume throughout this section that the residue extension

$ l:=B slash frak(q) quad "over" quad k:=A slash frak(p) $

is separable. Write

$ e:=e_(L slash K), quad f:=f_(L slash K), quad n=[L:K]=e f $

and let $p="char"(K)>=0$.

The ramification index measures how much one valuation step in $K$ is
subdivided inside $L$. Whether this subdivision is visible to first-order
calculus depends on whether $e$ is invertible in the residue field.

=== The Ramification Dictionary

#definition(title: "Tame and Wild Ramification")[
  Assume first that $p>0$.

  + The extension $L slash K$ is #emph[tamely ramified] if

    $ p divides.not e $

  + It is #emph[wildly ramified] if

    $ p divides e $

  + It is #emph[totally tamely ramified] if $f=1$ and
    $p divides.not e$.

  + It is #emph[totally wildly ramified] if $f=1$ and $e$ is a power of
    $p$.

  When $p=0$, every finite extension with separable residue extension is
  tamely ramified and wild ramification does not occur.
]

Every unramified extension is tame, since its ramification index is $1$.
When $p>0$ and the residue extension is separable, tame and wild are mutually
exclusive and exhaust all possibilities.

The word #emph[totally] in “totally wildly ramified” includes two separate
requirements: the residue field is unchanged, and the entire degree is a
power of the residue characteristic. Thus a totally ramified extension can
be wild without being totally wildly ramified.

#block(breakable: false)[
  #align(center, table(
    columns: (1.15fr, 1.1fr, 1.3fr),
    align: (center, center, left),
    inset: (x: 10pt, y: 5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[Behavior]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Numerical condition]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Arithmetic meaning]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    [unramified], [$e=1$], [only the residue field changes],
    [tamely ramified], [$p divides.not e$], [$e$ remains invertible in $k$],
    [wildly ramified], [$p divides e$], [the derivative can vanish modulo $frak(q)$],
    [totally ramified], [$f=1$], [only the value group changes],
    [totally tame], [$f=1, p divides.not e$], [a radical of a uniformizer],
    [totally wild], [$f=1, e=p^a$], [purely wild valuation growth],
  ))
]

#remark(title: "Why Tame Means Controllable")[
  Suppose a construction leads to an equation

  $ X^e-u=0 $

  with $u equiv 1 mod frak(q)$. At the residue root $X=1$, the derivative is
  $e$. In the tame case $p divides.not e$, this derivative is a unit, so
  Hensel's lemma extracts an $e$th root of $u$. In the wild case
  $p divides e$, the derivative vanishes on the closed fiber and this simple
  lifting argument loses its force.

  #quote[
    Tame ramification is ramification whose multiplicity is still visible to
    the derivative; wild ramification begins when characteristic $p$ erases
    that multiplicity.
  ]
]

#example(title: "Three Basic Eisenstein Behaviors")[
  Let $K=QQ_p$.

  + If $gcd(n,p)=1$, then $X^n-p$ defines a totally tamely ramified extension
    of degree $n$.

  + The polynomial $X^p-p$ defines a totally wildly ramified extension of
    degree $p$.

  + For $p=3$, the polynomial $X^6-3$ is Eisenstein and defines a totally
    ramified extension of degree $6$. It is wildly ramified because
    $3 divides 6$, but it is not totally wildly ramified because $6$ is not a
    power of $3$.
]

=== Behavior in Towers and Composita

#proposition(title: "Transitivity in Towers")[
  Let

  $ K subset.eq E subset.eq L $

  be a tower of finite extensions of fraction fields of complete DVRs, with
  separable residue extensions. If both layers have any one of the following
  properties, then the full extension $L slash K$ has the same property:

  + unramified;

  + tamely ramified;

  + wildly ramified;

  + totally ramified;

  + totally tamely ramified;

  + totally wildly ramified.
]

#proof[
  Ramification indices and residue degrees multiply:

  $ e_(L slash K)=e_(L slash E)e_(E slash K) $

  $ f_(L slash K)=f_(L slash E)f_(E slash K) $

  Separability is transitive in residue-field towers. Products of integers
  prime to $p$ remain prime to $p$, products of integers divisible by $p$
  remain divisible by $p$, and products of powers of $p$ remain powers of
  $p$. Each assertion follows from these observations.
]

#remark(title: "Transitive Does Not Mean Two-Way")[
  If $L slash K$ is wildly ramified, one of the two layers in a tower must be
  wild, but both need not be. Likewise, a tame extension may contain a
  nontrivial unramified layer followed by a totally tame layer. The
  proposition only asserts that a property shared by both layers survives
  composition.
]

#example(title: "Totally Ramified Composita Need Not Be Totally Ramified")[
  Over $QQ_3$, both

  $ QQ_3 (sqrt(3)) slash QQ_3, quad QQ_3 (sqrt(6)) slash QQ_3 $

  are totally tamely ramified quadratic extensions, defined by Eisenstein
  polynomials. Their compositum contains

  $ sqrt(2)=sqrt(3)sqrt(6)/3 $

  and $QQ_3 (sqrt(2)) slash QQ_3$ is the unramified quadratic extension.
  Therefore the compositum is not totally ramified over $QQ_3$.

  The failure comes from combining different valuation directions: their
  quotient can cancel the ramified part and expose a residue-field extension.
]

=== Classification of Totally Tame Extensions

The tame case admits an exceptionally concrete classification: after changing
the chosen uniformizer of the base by a unit, the whole extension is obtained
by taking one radical.

#theorem(title: "Totally Tame Extensions Are Radicals of a Uniformizer")[
  Let $L slash K$ have degree $n$, and suppose the residue extension is
  separable of characteristic $p>=0$ with $p divides.not n$ when $p>0$.
  Then the following are equivalent.

  + The extension $L slash K$ is totally tamely ramified.

  + For some uniformizer $pi_A$ of $A$,

    $ L=K(pi_A^(1\/n)) $

  In this description $X^n-pi_A$ is Eisenstein, and
  $pi_A^(1\/n)$ is a uniformizer of $B$.
]

#proof[
  If $L=K(pi_A^(1\/n))$, the polynomial $X^n-pi_A$ is Eisenstein. It defines a
  totally ramified extension of degree $n$, and the hypothesis
  $p divides.not n$ makes the extension tame.

  Conversely, assume that $L slash K$ is totally tamely ramified. Choose
  uniformizers $pi_A$ of $A$ and $pi_B$ of $B$. Since

  $ v_(frak(q)) (pi_B^n)=n=v_(frak(q)) (pi_A) $

  there is a unit $u in B^times$ such that

  $ pi_B^n=u pi_A $

  The residue fields are equal. Choose $u_A in A^times$ whose residue equals
  that of $u$, and replace $pi_A$ by $u_A pi_A$. After replacing $u$ by
  $u/u_A$, we may assume

  $ u equiv 1 mod frak(q) $

  Consider $g(X)=X^n-u in B[X]$. Its reduction has the root $1$, and

  $ overline(g)'(1)=n!=0 " in " k $

  because $p divides.not n$. Hensel's lemma gives $r in B^times$ satisfying
  $r equiv 1 mod frak(q)$ and $r^n=u$. Put

  $ pi:=pi_B/r $

  Then $pi$ is a uniformizer of $B$ and

  $ pi^n=pi_B^n/r^n=pi_A $

  Every uniformizer generates a totally ramified extension, by the preceding
  section, so

  $ L=K(pi)=K(pi_A^(1/n)) $
]

#remark(title: "What Is and Is Not Canonical")[
  The totally tame extension is generated by an $n$th root of
  #emph[some] uniformizer, not necessarily the first uniformizer one writes
  down. Multiplying $pi_A$ by a unit changes the radical equation. Hensel's
  lemma absorbs precisely the principal-unit part that is an $n$th power.
]

#example(title: [The Ramified Quadratic Extensions of $QQ_3$])[
  The two extensions

  $ QQ_3 (sqrt(3)), quad QQ_3 (sqrt(6)) $

  are totally tamely ramified of degree $2$. They correspond to the two
  uniformizers $3$ and $6=2 dot 3$. The unit $2$ represents the nontrivial
  square class in $FF_3^times$, so the two radical extensions are not
  $QQ_3$-isomorphic inside a fixed algebraic closure.
]

=== Separating the Tame and Wild Parts

For a totally ramified extension, factor the degree as

$ e=m p^a, quad gcd(m,p)=1 $

when $p>0$. The prime-to-$p$ part and the $p$-power part are realized by a
unique intermediate field.

#theorem(title: [The Tame--Wild Decomposition in the Totally Ramified Case])[
  Let $L slash K$ be totally ramified. There is a unique intermediate field
  $E$ such that

  + $E slash K$ is totally tamely ramified;

  + $L slash E$ is totally wildly ramified.

  More precisely, if

  $ [L:K]=m p^a, quad gcd(m,p)=1 $

  then

  $ [E:K]=m, quad [L:E]=p^a $

  When the residue characteristic is zero, take $E=L$.
]

#proof[
  Assume $p>0$; the characteristic-zero case is immediate. Choose
  uniformizers $pi_A$ of $A$ and $pi_B$ of $B$. As in the totally tame
  classification, write

  $ pi_B^(m p^a)=u pi_A $

  and multiply $pi_A$ by the lift of the residue of $u$ so that
  $u equiv 1 mod frak(q)$. Since $p divides.not m$, Hensel's lemma gives a
  unit $r in B^times$ with

  $ r^m=u $

  Put

  $ pi_E:=pi_B^(p^a)/r $

  Then

  $ pi_E^m=pi_B^(m p^a)/r^m=pi_A $

  and define $E:=K(pi_E)$. The polynomial $X^m-pi_A$ is Eisenstein, so
  $[E:K]=m$ and $E slash K$ is totally tamely ramified. It follows that

  $ [L:E]=p^a $

  and, since the residue field remains unchanged throughout the tower,
  $L slash E$ is totally wildly ramified.

  For uniqueness, let $E'$ have the same two properties. Multiplicativity of
  degrees forces

  $ [E':K]=m, quad [L:E']=p^a $

  Repeating the construction with the fixed relation
  $pi_B^(m p^a)=u pi_A$ shows that $E'$ is generated by another $m$th root
  $pi_E'$ of the same uniformizer $pi_A$. Hence

  $ zeta:=pi_E' slash pi_E $

  is an $m$th root of unity contained in $L$. Because $p divides.not m$, the
  extension $K(zeta) slash K$ is unramified. But it is also a subextension of
  the totally ramified extension $L slash K$, so it must be trivial. Thus
  $zeta in K$, and $E'=E$.
]

#remark(title: "Why an Extension Cannot Be Both Nontrivially Unramified and Totally Ramified")[
  Any subextension of a totally ramified extension has residue degree $1$.
  An unramified subextension has ramification index $1$. The fundamental
  identity then forces its degree to be $1$. This tiny observation is the
  rigidity behind the uniqueness argument.
]

#corollary(title: "The Maximal Tame Subextension")[
  Let $L slash K$ be any finite separable extension with separable residue
  extension. There is a unique intermediate field $E$ such that

  + $E slash K$ is tamely ramified;

  + $L slash E$ is totally wildly ramified.

  If $F$ is the maximal unramified subextension of $L slash K$ and

  $ e_(L slash K)=m p^a, quad gcd(m,p)=1 $

  then

  $ [F:K]=f, quad [E:F]=m, quad [L:E]=p^a $
]

#proof[
  The extension $L slash F$ is totally ramified. Apply the totally ramified
  tame--wild decomposition to obtain

  $ F subset.eq E subset.eq L $

  with $E slash F$ totally tame and $L slash E$ totally wild. Since
  $F slash K$ is unramified, it is tame; transitivity in towers shows that
  $E slash K$ is tame.

  Conversely, suppose $E'$ is tame and $L slash E'$ is totally wild. The
  field $E'$ must contain $F$: otherwise the compositum $E'F slash E'$ would
  be a nontrivial unramified subextension of the totally ramified extension
  $L slash E'$. Once $F subset.eq E'$, uniqueness of the totally ramified
  decomposition for $L slash F$ gives $E'=E$.
]

#remark(title: "Galois-Theoretic Preview")[
  If $L slash K$ is Galois, the subgroup

  $ "Gal"(L slash E) $

  is the $p$-primary part of the inertia group. It is called the
  #emph[wild inertia group]. The quotient retains the unramified and tame
  directions, while this subgroup measures the genuinely characteristic-$p$
  obstruction.
]

#quote[
  Every finite extension with separable residue extension has a unique tame
  layer; everything above it is totally wild.
]

== Krasner's Lemma

Hensel's lemma says that an approximate root with nonvanishing derivative
determines an exact root. Krasner's lemma answers a different question:
when an algebraic number $beta$ is sufficiently close to another algebraic
number $alpha$, how are the fields $K(beta)$ and $K(alpha)$ related?

The answer is strikingly rigid. If $beta$ lies closer to $alpha$ than to any
other conjugate of $alpha$, then $beta$ already remembers $alpha$:

$ K(alpha) subset.eq K(beta) $

=== Conjugate Distances and the Krasner Radius

Let $K$ be the fraction field of a complete DVR. Its absolute value extends
uniquely to a fixed algebraic closure $overline(K)$.

#lemma(title: "Galois Invariance of the Absolute Value")[
  For every $sigma in Aut_K (overline(K))$ and every
  $gamma in overline(K)$,

  $ abs(sigma(gamma))=abs(gamma) $

  Consequently,

  $ abs(sigma(gamma)-sigma(delta))=abs(gamma-delta) $

  for all $gamma,delta in overline(K)$.
]

#proof[
  The map

  $ gamma mapsto abs(sigma(gamma)) $

  is another absolute value on $overline(K)$ extending the given absolute
  value on $K$. Uniqueness of the extension makes it equal to
  $abs(dot)$. Applying this to $gamma-delta$ proves the second formula.
]

#remark(title: "A Galois Automorphism Relabels without Stretching")[
  Think of the conjugates of an algebraic element as a finite constellation
  of points. A $K$-automorphism may permute the labels on these points, but it
  cannot stretch or shrink the constellation: every pairwise distance is
  preserved.

  This is special to the complete henselian setting. The absolute value has a
  unique extension to $overline(K)$, so applying an automorphism cannot
  secretly replace it by a different notion of size.
]

#definition(title: "Krasner Radius")[
  Let $alpha in overline(K)$ be separable over $K$. Its
  #emph[Krasner radius] is

  $ rho_K (alpha):=min_(sigma(alpha)!=alpha) abs(alpha-sigma(alpha)) $

  where $sigma$ runs through $Aut_K (overline(K))$. If
  $alpha in K$, we put $rho_K (alpha)=infinity$.

  Thus $rho_K (alpha)$ is the distance from $alpha$ to its nearest distinct
  $K$-conjugate.
]

Separability is essential here: it makes the conjugates distinct, and there
are only finitely many of them. Hence
$rho_K (alpha)>0$ whenever $alpha$ is separable.

#remark(title: "Nearest-Neighbor Safety Radius")[
  The number $rho_K (alpha)$ is simply the distance from $alpha$ to its
  nearest competitor among the other conjugates. Moving by strictly less than
  this amount cannot reach, or even become confused with, another conjugate.

  It is useful to picture a label attached to $alpha$ together with a safety
  zone of radius $rho_K (alpha)$. Any point inside this zone still knows which
  conjugate it is approximating.
]

#definition(title: "Belonging to an Algebraic Element")[
  Let $alpha,beta in overline(K)$, with $alpha$ separable over $K$. We say
  that #emph[$beta$ belongs to $alpha$] if

  $ abs(beta-alpha)<abs(beta-sigma(alpha)) $

  for every $sigma in Aut_K (overline(K))$ with
  $sigma(alpha)!=alpha$.
]

#proposition(title: "Equivalent Distance Form")[
  The element $beta$ belongs to $alpha$ if and only if

  $ abs(beta-alpha)<rho_K (alpha) $

  Equivalently,

  $ abs(beta-alpha)<abs(alpha-sigma(alpha)) $

  for every distinct conjugate $sigma(alpha)$.
]

#proof[
  Suppose

  $ abs(beta-alpha)<abs(alpha-sigma(alpha)) $

  The ultrametric triangle with vertices
  $alpha,beta,sigma(alpha)$ has one side strictly shorter than another, so
  the two longer sides have equal length:

  $ abs(beta-sigma(alpha))=abs(alpha-sigma(alpha)) $

  Hence $beta$ belongs to $alpha$. Conversely, if
  $abs(beta-alpha)<abs(beta-sigma(alpha))$, the same rigid-triangle argument
  gives

  $ abs(alpha-sigma(alpha))=abs(beta-sigma(alpha)) $

  and therefore
  $abs(beta-alpha)<abs(alpha-sigma(alpha))$. Taking the minimum over all
  distinct conjugates proves the claim.
]

#remark(title: "The Ultrametric Shortcut")[
  In ordinary Euclidean geometry, moving $alpha$ slightly changes its
  distance to every other point by a small amount. Ultrametric geometry is
  more rigid. If

  $ abs(beta-alpha)<abs(alpha-sigma(alpha)) $

  then the short move from $alpha$ to $beta$ does not change the longer
  distance at all:

  $ abs(beta-sigma(alpha))=abs(alpha-sigma(alpha)) $

  Thus the perturbation is invisible from the viewpoint of every other
  conjugate. This rigid-isosceles phenomenon is why the two formulations of
  “belongs to” are exactly equivalent rather than merely comparable.
]

#remark(title: "The Conjugate Balls Are Disjoint")[
  For every conjugate $alpha_i$ of $alpha$, consider

  $ B_i:={x in overline(K):abs(x-alpha_i)<rho_K (alpha)} $

  These balls are pairwise disjoint. If one point belonged to both
  $B_i$ and $B_j$, the ultrametric inequality would give

  $ abs(alpha_i-alpha_j)<rho_K (alpha) $

  contradicting the definition of the radius. Thus a point inside one of
  these balls identifies one conjugate unambiguously.
]

If $f in K[X]$ is the separable minimal polynomial of $alpha$, then

$ f'(alpha)=product_(sigma(alpha)!=alpha) (alpha-sigma(alpha)) $

The derivative therefore measures the product of all conjugate separations,
while the Krasner radius records the smallest one. Hensel's lemma and
Krasner's lemma are controlled by two closely related measures of how
isolated a root is.

#remark(title: "Product versus Bottleneck")[
  The derivative $f'(alpha)$ combines #emph[all] conjugate distances into one
  product. The Krasner radius keeps only the smallest distance, because the
  nearest conjugate is the first one with which a perturbation could be
  confused.

  In this sense, Hensel's derivative is an aggregate separation measure,
  while the Krasner radius is the bottleneck separation.
]

=== Statement and Proof

#theorem(title: "Krasner's Lemma")[
  Let $K$ be the fraction field of a complete DVR, and let
  $alpha,beta in overline(K)$ with $alpha$ separable over $K$. If $beta$
  belongs to $alpha$, equivalently if

  $ abs(beta-alpha)<rho_K (alpha) $

  then

  $ K(alpha) subset.eq K(beta) $
]

#remark(title: "The Proof in One Sentence")[
  If $beta$ did not determine $alpha$, there would remain a symmetry that
  fixes $beta$ but moves $alpha$ to another conjugate; distance preservation
  would then make $beta$ equally close to both, contradicting the strict
  nearest-conjugate condition.
]

#proof[
  Suppose instead that $alpha in.not K(beta)$. Then the minimal polynomial of
  $alpha$ over $K(beta)$ has degree greater than one. Since $alpha$ is
  separable over $K$, it is also separable over $K(beta)$. There is therefore
  a $K(beta)$-embedding of $K(alpha,beta)$ into $overline(K)$ that sends
  $alpha$ to a distinct conjugate. Extend it to an automorphism

  $ sigma in Aut_(K(beta)) (overline(K)) $

  Thus $sigma(beta)=beta$ but $sigma(alpha)!=alpha$. Galois invariance of the
  absolute value gives

  $ abs(beta-alpha)=abs(sigma(beta-alpha))=abs(beta-sigma(alpha)) $

  This contradicts the assumption that $beta$ belongs to $alpha$. Hence
  $alpha in K(beta)$ and $K(alpha) subset.eq K(beta)$.
]

#remark(title: "Why the Inclusion Points This Way")[
  The hypothesis says that $beta$ contains enough information to identify
  the particular conjugate $alpha$. It does not say that $alpha$ contains all
  the information carried by $beta$. Thus Krasner gives

  $ K(alpha) subset.eq K(beta) $

  rather than the reverse inclusion.

  One may think of $beta$ as a very accurate measurement of $alpha$ together
  with some additional algebraic data. The accuracy recovers $alpha$, while
  the extra data may make $K(beta)$ strictly larger.
]

#quote[
  A sufficiently accurate algebraic approximation cannot forget the field
  generated by the conjugate it approximates.
]

=== Immediate Consequences

#corollary(title: "Equality from a Degree Bound")[
  Let $n=[K(alpha):K]$. If

  $ abs(beta-alpha)<rho_K (alpha) $

  and $[K(beta):K]<=n$, then

  $ K(beta)=K(alpha) $
]

#proof[
  Krasner's lemma gives

  $ K(alpha) subset.eq K(beta) $

  Hence

  $ n<=[K(beta):K]<=n $

  so equality holds throughout.
]

#remark(title: "The Degree Squeeze")[
  Krasner supplies the difficult half, namely the field inclusion. Once this
  is known, degrees turn it into equality:

  $ [K(alpha):K]<=[K(beta):K] $

  If an independent argument bounds the right-hand side by the left-hand
  side, there is no room for a proper extension. This simple squeeze is the
  standard way Krasner's lemma is used in practice.
]

#corollary(title: "Stability of Primitive Elements")[
  Let $L=K(alpha)$ be finite separable. Every algebraic
  $beta in overline(K)$ satisfying

  $ abs(beta-alpha)<rho_K (alpha), quad [K(beta):K]<=[L:K] $

  also generates $L$.
]

This is the practical form used most often: once a primitive element is
separated from its other conjugates, every sufficiently close algebraic
element of no larger degree defines the same extension.

#example(title: [A Krasner Ball around $sqrt(p)$])[
  Let $p$ be odd and put

  $ K=QQ_p, quad alpha=sqrt(p) $

  The two conjugates are $alpha$ and $-alpha$, so

  $ rho_K (alpha)=abs(2alpha)_p=abs(alpha)_p=p^(-1/2) $

  Therefore every algebraic $beta in overline(QQ_p)$ with

  $ abs(beta-sqrt(p))_p<p^(-1/2) $

  satisfies

  $ QQ_p (sqrt(p)) subset.eq QQ_p (beta) $

  If $beta$ has degree at most two over $QQ_p$, the two fields are equal.
]

#remark(title: "The Inequality Must Be Strict")[
  If $beta$ lies exactly on the boundary
  $abs(beta-alpha)=rho_K (alpha)$, it may be equally close to two conjugates.
  Then the preferred branch is no longer determined, and the conclusion of
  Krasner's lemma can fail. The strict inequality is the nonarchimedean
  analogue of staying inside one isolated component.
]

#remark(title: "A Nonarchimedean Voronoi Cell")[
  In elementary geometry, a Voronoi cell consists of the points closest to
  one chosen center. The condition

  $ abs(beta-alpha)<rho_K (alpha) $

  places $beta$ inside a particularly simple nonarchimedean Voronoi cell
  around $alpha$. The strict boundary separates this cell from those of all
  other conjugates. Krasner's lemma says that belonging to this metric cell
  has an algebraic consequence: the field of its center is forced into the
  field of the point.
]

=== What Krasner's Lemma Does

Krasner's lemma is less an algorithm for finding roots than a stability
principle for field extensions.

+ #emph[It turns metric closeness into field containment.] The hypothesis is
  expressed entirely using distances, but the conclusion is the algebraic
  inclusion $K(alpha) subset.eq K(beta)$.

+ #emph[It makes primitive elements stable.] Small perturbations of a
  primitive element continue to generate the same field, once their degrees
  cannot increase.

+ #emph[It makes roots continuous in the correct sense.] If the coefficients
  of a separable irreducible polynomial are perturbed slightly, its roots
  remain in disjoint Krasner balls around the original roots. Matching
  degrees then shows that the perturbed polynomial defines the same field
  extension and has the same splitting field.

+ #emph[It connects local and global fields.] Coefficients in a completion
  can be approximated by coefficients in the dense global field. Krasner's
  lemma ensures that a sufficiently close global polynomial realizes the
  prescribed local extension after completion.

+ #emph[It explains local constancy.] Finite separable extensions do not vary
  continuously through infinitely many different algebraic types under tiny
  coefficient perturbations; within a sufficiently small neighborhood, the
  generated extension is constant.

#remark(title: "Geometric Reading")[
  The conjugates of $alpha$ are the geometric points in the generic fiber of
  the finite étale algebra defined by its minimal polynomial. The disjoint
  Krasner balls are analytic neighborhoods separating these points. Placing
  $beta$ inside the ball around $alpha$ selects one branch, and Krasner's
  lemma says that this analytic choice forces the corresponding algebraic
  field to be present inside $K(beta)$.
]

#quote[
  Hensel lifts an isolated residue root; Krasner preserves an isolated
  conjugate under perturbation.
]
