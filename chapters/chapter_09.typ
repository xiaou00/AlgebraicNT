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

  the absolute value $x mapsto c^(v_(frak(q)) (x)/e)$ extends
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

#corollary(title: "Local Dedekind--Kummer")[
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
