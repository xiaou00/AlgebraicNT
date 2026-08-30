#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Completions

Chapter 6 attached topologies to valuations and absolute values. We now ask
the corresponding analytic question: if a sequence becomes arbitrarily
accurate, must it converge to an element already present? A completion fills
exactly these missing limits. There are two constructions to compare:
completion of a ring along an ideal, and completion of a field with respect
to an absolute value.

#quote[
  Completion replaces finite-precision approximations by the object that
  contains every compatible approximation at once.
]

== Ideal-adic Topology and Completion

=== The $I$-adic Topology

#definition(title: [The $I$-adic Topology])[
  Let $A$ be a commutative ring and $I subset.eq A$ an ideal. The
  #emph[$I$-adic topology] on $A$ is the topology for which

  $ I,I^2,I^3,dots $

  form a neighborhood basis at $0$. Equivalently, the basic neighborhoods of
  $a in A$ are the cosets

  $ a+I^n, quad n>=1 $

  A sequence $(a_m)$ is #emph[$I$-adically Cauchy] if, for every $n$, there
  exists $M$ such that

  $ r,s>=M => a_r-a_s in I^n $
]

The topology records congruence with increasing precision. Two elements are
close when their difference lies in a high power of $I$; no numerical distance
is needed.

#proposition(title: "Basic Topological Properties")[
  The $I$-adic topology makes $A$ a topological ring. Each $I^n$ is both open
  and closed, and the topology is Hausdorff if and only if

  $ inter.big_(n>=1) I^n={0} $
]

#proof[
  Addition is continuous because sums and differences preserve congruence
  modulo $I^n$. If $x-x',y-y' in I^n$, then

  $ x y-x' y'=x(y-y')+y'(x-x') in I^n $

  so multiplication is continuous as well. Every $I^n$ is open by definition;
  its complement is a union of open cosets, hence it is closed. Finally, two
  points $x,y$ can be separated precisely when $x-y$ does not lie in every
  $I^n$, which is equivalent to the displayed intersection being zero.
]

#definition(title: "Separatedness")[
  The ring $A$ is #emph[$I$-adically separated] if
  $inter.big_(n>=1) I^n={0}$. In this case an element is uniquely determined by
  all of its residue classes modulo $I^n$.
]

#remark(title: "Geometric Meaning")[
  The closed subschemes

  $ Spec (A slash I) arrow.r.hook Spec (A slash I^2) arrow.r.hook Spec (A slash I^3) arrow.r.hook dots arrow.r.hook Spec A $

  have the same underlying closed set $V(I)$ but remember successively thicker
  infinitesimal neighborhoods. The $I$-adic viewpoint studies all these
  thickenings simultaneously. Its geometric avatar is the formal neighborhood
  $Spf hat(A)^I$ of $V(I)$ inside $Spec A$.
]

=== Construction by an Inverse Limit

#definition(title: [The $I$-adic Completion])[
  The #emph[$I$-adic completion] of $A$ is

  $ hat(A)^I:=varprojlim(n) A slash I^n $

  where the transition maps are the natural quotient maps

  $ A slash I^(n+1)->A slash I^n $

  Thus an element of $hat(A)^I$ is a compatible system

  $ (alpha_n)_(n>=1), quad alpha_n in A slash I^n, quad alpha_(n+1) mod I^n=alpha_n $

  with addition and multiplication defined coordinatewise.
]

There is a canonical homomorphism

  $ iota_A:A->hat(A)^I, quad a mapsto (a mod I^n)_(n>=1) $

It need not be injective or surjective: these two possible failures are
exactly separatedness and completeness.

#theorem(title: "The Canonical Map")[
  For the canonical map $iota_A:A->hat(A)^I$:

  + $ker(iota_A)=inter.big_(n>=1) I^n$;

  + the image of $A$ is dense in $hat(A)^I$;

  + $hat(A)^I$ is separated and complete for its inverse-limit topology.

  Consequently, $A$ is $I$-adically separated and complete if and only if
  $iota_A$ is an isomorphism.
]

#proof[
  An element $a$ maps to zero exactly when $a in I^n$ for every $n$, proving
  the kernel formula. Let $alpha=(alpha_n)$ be a compatible system. For a
  fixed $N$, choose a lift $a in A$ of $alpha_N$. Then $iota_A (a)$ and
  $alpha$ have the same first $N$ coordinates, which proves density.

  A Cauchy sequence in the inverse limit is eventually constant in each
  quotient $A slash I^n$. Its eventual values form a compatible system, hence
  a limit in $hat(A)^I$. If all coordinates of an element vanish, the element
  itself is zero, so the completion is separated. The final assertion follows
  from the kernel formula and the definition of completeness.
]

#remark(title: "The Meaning of Surjectivity")[
  Surjectivity of $iota_A$ says that every compatible tower

  $ a_1 mod I, quad a_2 mod I^2, quad a_3 mod I^3, quad dots $

  comes from one element $a in A$. Injectivity says that this element is unique.
  Thus completion is an existence statement, while separatedness is a
  uniqueness statement.
]

#proposition(title: "Functoriality and the Universal Property")[
  Let $f:A->B$ be a ring homomorphism and let $I subset.eq A$, $J subset.eq B$
  be ideals satisfying $f(I) subset.eq J$. Then $f$ induces a continuous map

  $ hat(f):hat(A)^I->hat(B)^J $

  If $B$ is $J$-adically separated and complete, every such continuous map
  $A->B$ extends uniquely across the dense map $A->hat(A)^I$.
]

#proof[
  Since $f(I^n) subset.eq J^n$, the maps

  $ A slash I^n->B slash J^n $

  commute with the transition maps. Taking inverse limits gives $hat(f)$.
  If $B tilde.eq hat(B)^J$, this construction gives the required extension.
  Uniqueness follows because $A$ is dense in $hat(A)^I$ and $B$ is Hausdorff.
]

#remark(title: "Modules")[
  For an $A$-module $M$, the same construction gives

  $ hat(M)^I:=varprojlim(n) M slash I^n M $

  This is the module-theoretic analogue of completing a normed vector space.
  For finitely generated modules over a Noetherian ring, completion behaves
  especially well; this is one of the main algebraic uses of the construction.
]

=== Formal Neighborhoods and Infinitesimal Information

Let $X=Spec A$ and let $Z=V(I)=Spec (A slash I)$. For $n>=0$, put

$ Z_n:=Spec (A slash I^(n+1)) $

All the schemes $Z_n$ have the same underlying topological space $Z$, since
$sqrt(I^(n+1))=sqrt(I)$. What changes with $n$ is the nilpotent structure:
$Z_n$ remembers functions modulo terms vanishing to order $n+1$ along $Z$.

#proposition(title: "Successive Infinitesimal Thickenings")[
  For $n>=1$, the closed immersion

  $ Z_(n-1) arrow.r.hook Z_n $

  is a square-zero thickening controlled by the module

  $ I^n slash I^(n+1) $

  In particular, $I slash I^2$ is the first-order #emph[conormal module] of
  $Z$ in $X$, while the quotients $I^n slash I^(n+1)$ record higher-order
  normal information.
]

#proof[
  The kernel of

  $ A slash I^(n+1)->A slash I^n $

  is $I^n slash I^(n+1)$. Its square vanishes because
  $I^(2n) subset.eq I^(n+1)$ for $n>=1$. The first-order case $n=1$ gives
  $I slash I^2$, and the same calculation describes every higher layer.
]

#quote[
  $I$-adic completion does not merely restrict functions to $Z$; it remembers
  their behavior to every infinitesimal order transverse to $Z$.
]

The completion collects the rings of functions on all thickenings:

$ hat(A)^I=varprojlim(n) Gamma(Z_n,cal(O)_(Z_n)) $

Thus $Spf hat(A)^I$ should be read as the #emph[formal neighborhood] of $Z$ in
$X$. It zooms indefinitely toward $Z$ without adding ordinary points away
from $Z$.

#example(title: "The Formal Disk at a Point")[
  Let $A=k[t]$ and $I=(t)$. Then

  $ A slash I^n=k[t] slash (t^n), quad hat(A)^I tilde.eq k[[t]] $

  The quotient $k[t] slash (t^n)$ remembers a polynomial only through its first
  $n$ coefficients at $t=0$. Passing to the limit produces

  $ f(t)=c_0+c_1 t+c_2 t^2+dots $

  Here $c_0$ is the value at the point, while $c_1,c_2,dots$ encode all higher
  infinitesimal jets. The formal scheme $Spf k[[t]]$ is therefore a disk made
  from infinitesimal neighborhoods rather than additional nearby points.
]

#example(title: "The Formal Neighborhood of a Line")[
  Let $A=k[x,y]$ and $I=(y)$, so that $V(I)$ is the $x$-axis. Then

  $ hat(A)^I tilde.eq k[x][[y]] $

  An element has the form

  $ f_0(x)+f_1(x)y+f_2(x)y^2+dots $

  The coefficient $f_0(x)$ is the restriction to the line, while the remaining
  coefficients record every order of variation in the normal $y$-direction.
  This is the geometric content hidden in the inverse limit.
]

== $p$-adic Rings

Fix a prime number $p$. For every ring $A$, the structure map $ZZ->A$ gives
an element again denoted by $p$. We now specialize the preceding construction
to the principal ideal $(p)$.

#definition(title: [$p$-adic Ring])[
  A ring $A$ is a #emph[$p$-adic ring] if the canonical map

  $ A->varprojlim(n) A slash p^n A $

  is an isomorphism. Equivalently, $A$ is separated and complete for the
  $p$-adic topology whose basic neighborhoods of $0$ are $p^n A$.
]

#quote[
  An element of a $p$-adic ring is a compatible answer modulo $p^n$ at every
  finite precision $n$.
]

The definition contains two logically different requirements:

+ #emph[separatedness] says that two elements agreeing modulo every $p^n$ are
  equal;

+ #emph[completeness] says that every coherent family of finite-precision
  answers is represented by an element of the ring.

=== Equivalent Characterizations

#theorem(title: [Equivalent Definitions of a $p$-adic Ring])[
  For a ring $A$, the following conditions are equivalent.

  + The canonical map

    $ A->varprojlim(n) A slash p^n A $

    is an isomorphism.

  + One has $inter.big_(n>=1) p^n A={0}$, and every $p$-adically Cauchy
    sequence converges in $A$.

  + For every compatible system

    $ alpha_n in A slash p^n A, quad alpha_(n+1) mod p^n=alpha_n $

    there exists a unique $a in A$ satisfying

    $ a mod p^n=alpha_n quad "for every" n $

  + The ring is $p$-adically separated, and every series

    $ sum_(n=0)^infinity p^n b_n, quad b_n in A $

    converges in $A$.
]

#proof[
  The first and third conditions are two descriptions of the same inverse
  limit: injectivity gives uniqueness and surjectivity gives existence.

  Suppose the third condition holds. Given a Cauchy sequence $(x_m)$, choose
  indices

  $ m_1<m_2<dots $

  such that $x_r equiv x_(m_n) mod p^n$ whenever $r>=m_n$. The classes of
  $x_(m_n)$ form a compatible system, hence come from a unique $x in A$. The
  subsequence converges to $x$, and the Cauchy condition then forces the whole
  sequence to converge to $x$. Uniqueness implies
  $inter.big_(n>=1) p^n A={0}$.

  Conversely, a compatible system of representatives $(a_n)$ is Cauchy:
  whenever $m>=n$, one has $a_m-a_n in p^n A$. By the second condition it
  converges to some $a$. Since $p^n A$ is closed, $a-a_n in p^n A$ for every
  $n$; separatedness gives uniqueness. Thus the second and third conditions
  are equivalent.

  Every series in the fourth condition has Cauchy partial sums, so the second
  condition implies the fourth. Conversely, choose representatives of a
  compatible system with

  $ a_(n+1)-a_n=p^n b_n $

  Then

  $ a_N=a_1+sum_(n=1)^(N-1) p^n b_n $

  and convergence of the series produces the required common lift. This proves
  the final equivalence.
]

#remark(title: "Digit-by-Digit Lifting")[
  The proof gives a practical construction. First solve a problem modulo $p$,
  then correct the answer by a multiple of $p$ to solve it modulo $p^2$, then
  by a multiple of $p^2$ to solve it modulo $p^3$, and so on. Completeness turns
  the infinite sequence of corrections into an actual element. Hensel lifting
  is the most important nonlinear version of this pattern.
]

=== Examples and Nonexamples

#example(title: [The Ring $ZZ_p$])[
  The prototype is

  $ ZZ_p:=varprojlim(n) ZZ slash p^n ZZ $

  Every element has a unique digit expansion

  $ a=a_0+a_1 p+a_2 p^2+dots, quad 0<=a_i<p $

  Two elements are close when many of their low-order digits agree. Unlike a
  real decimal expansion, the powers of $p$ extend indefinitely toward larger
  exponents; the partial sums converge because the tail is divisible by an
  arbitrarily large power of $p$.
]

#example(title: "A Ring That Is Not Yet Complete")[
  The localization $ZZ_((p))$ is $p$-adically separated but not complete. Its
  completion is $ZZ_p$:

  $ hat(ZZ_((p)))^((p)) tilde.eq ZZ_p $

  Thus completion adds limits without changing any finite quotient modulo
  $p^n$.
]

#example(title: [Nilpotent and Characteristic-$p$ Examples])[
  If $p^r A=0$ for some $r$, the $p$-adic topology is discrete after finitely
  many steps and $A$ is automatically $p$-adic. In particular,
  $ZZ slash p^r ZZ$ and every $FF_p$-algebra are $p$-adic rings. This shows
  that a $p$-adic ring need not be a domain, local, or of characteristic zero.
]

#example(title: "Power-Series Rings")[
  The ring $ZZ_p [[T]]$ is $p$-adically complete: reduction modulo $p^n$ and
  inverse limits may be performed coefficientwise. In contrast, $ZZ_p [T]$ is
  not complete. Its completion is the restricted power-series ring

  $ ZZ_p lr(⟨ T ⟩):={sum_(i=0)^infinity a_i T^i : a_i in ZZ_p, a_i->0  space p"-adically"} $

  Indeed, modulo $p^n$ only finitely many coefficients may remain nonzero, so
  the condition $a_i->0$ is exactly what is needed to be polynomial at every
  finite $p$-adic precision.
]

#example(title: "Why Separatedness Matters")[
  In $A=ZZ[1/p]$, multiplication by $p$ is invertible, so
  $p^n A=A$ for every $n$. The $p$-adic topology is indiscrete and

  $ varprojlim(n) A slash p^n A=0 $

  Thus the canonical map $A->hat(A)^((p))$ forgets everything. Completeness
  without separatedness would therefore be the wrong notion.
]

== Completion of Absolute-Valued Fields

We now replace congruence modulo $I^n$ by metric approximation. Let
$(K,abs(dot))$ be an absolute-valued field. As in Chapter 6, a sequence
$(x_n)$ is Cauchy if

$ abs(x_m-x_n)->0 quad "as" m,n->infinity $

and $K$ is complete if every Cauchy sequence converges.

#definition(title: "Completion of an Absolute-Valued Field")[
  A #emph[completion] of $(K,abs(dot))$ is a complete absolute-valued field
  $hat(K)$ together with an isometric embedding

  $ iota:K->hat(K) $

  whose image is dense. Isometric means

  $ abs(iota(x))=abs(x) quad "for every" x in K $
]

=== Construction from Cauchy Sequences

Let $C(K)$ be the ring of Cauchy sequences in $K$, with coordinatewise
addition and multiplication, and let

$ N(K):={(x_n) in C(K) : x_n->0} $

The set $N(K)$ is an ideal of $C(K)$. We define

$ hat(K):=C(K) slash N(K) $

Thus two Cauchy sequences represent the same point precisely when their
difference tends to zero.

#lemma(title: "Extension of the Absolute Value")[
  For every Cauchy sequence $(x_n)$, the real sequence $(abs(x_n))$ converges.
  The formula

  $ abs([(x_n)]):=lim_(n->infinity) abs(x_n) $

  is well-defined on $hat(K)$ and extends the absolute value of $K$.
]

#proof[
  The reverse triangle inequality gives

  $ abs(abs(x_m)-abs(x_n))<=abs(x_m-x_n) $

  so $(abs(x_n))$ is Cauchy in $RR$. If $(x_n)-(y_n)$ tends to zero, the same
  inequality shows that the two real limits agree. Multiplicativity and the
  triangle inequality pass to limits. Constant sequences give the original
  absolute value on $K$.
]

#theorem(title: "Existence of the Completion")[
  The quotient $hat(K)=C(K) slash N(K)$ is a field, its extended absolute value
  makes it complete, and the constant-sequence map

  $ iota:K->hat(K), quad x mapsto [(x,x,x,dots)] $

  is an isometric embedding with dense image. If the original absolute value
  is nonarchimedean, then so is the extended absolute value.
]

#proof[
  Let $xi=[(x_n)]$ be nonzero. By the preceding lemma,
  $abs(x_n)->r$ for some $r>=0$. If $r=0$, then $(x_n) in N(K)$, contrary to
  $xi!=0$. Hence $r>0$, so $x_n!=0$ and $abs(x_n)$ is bounded away from zero
  for all sufficiently large $n$. After changing finitely many terms, the
  sequence $(x_n^(-1))$ is defined and

  $ abs(x_m^(-1)-x_n^(-1))=abs(x_m-x_n)/(abs(x_m)abs(x_n))->0 $

  Thus $(x_n^(-1))$ is Cauchy and represents the inverse of $xi$. Therefore
  $hat(K)$ is a field.

  Constant sequences embed $K$ isometrically. If $xi=[(x_n)]$ and
  $epsilon>0$, then for sufficiently large $N$,

  $ abs(x_N-x_n)<epsilon $

  for all large $n$. Hence the constant element $iota(x_N)$ lies within
  $epsilon$ of $xi$, proving density.

  Now let $(xi_m)$ be a Cauchy sequence in $hat(K)$. By density, choose
  $a_m in K$ with

  $ abs(iota(a_m)-xi_m)<1/m $

  The sequence $(a_m)$ is Cauchy in $K$, so it defines an element
  $xi=[(a_m)] in hat(K)$. The same inequality shows that $xi_m->xi$; hence
  $hat(K)$ is complete. Finally, the strong triangle inequality passes to
  limits just as the ordinary triangle inequality does.
]

#theorem(title: "Universal Property and Uniqueness")[
  Let $L$ be a complete absolute-valued field and let $f:K->L$ be an isometric
  embedding. There is a unique isometric embedding

  $ hat(f):hat(K)->L $

  extending $f$, and its image is the closure of $f(K)$. Consequently, any two
  completions of $K$ are uniquely isometrically isomorphic over $K$.
]

#proof[
  For a Cauchy sequence $(x_n)$ in $K$, the sequence $(f(x_n))$ is Cauchy in
  $L$ and therefore converges. Define

  $ hat(f)([(x_n)]):=lim_(n->infinity) f(x_n) $

  This is well-defined, respects the field operations and absolute values, and
  extends $f$. Density of $K$ in $hat(K)$ forces uniqueness. Its image is
  complete and hence closed in $L$, while it contains $f(K)$ densely, so it is
  exactly $overline(f(K))$. Applying this to a second completion gives the
  unique isometric isomorphism.
]

#remark(title: "Equivalent Absolute Values Have the Same Completion")[
  If $abs(x)_2=abs(x)_1^s$ with $s>0$, then the two absolute values have the
  same Cauchy sequences and null sequences. Their completions are therefore
  canonically isomorphic as topological fields. Completion depends on the
  equivalence class of the absolute value, not on its normalization.
]

=== First Examples

#example(title: "Archimedean Completion")[
  Completing $QQ$ with respect to its usual absolute value gives $RR$:

  $ hat(QQ)^(abs(dot)_infinity) tilde.eq RR $

  The familiar construction of real numbers from Cauchy sequences of rational
  numbers is exactly the preceding theorem.
]

#example(title: [$p$-adic Completion])[
  Completing $QQ$ with respect to $abs(dot)_p$ defines the field of $p$-adic
  numbers:

  $ QQ_p:=hat(QQ)^(abs(dot)_p) $

  Its closed unit ball is

  $ {x in QQ_p : abs(x)_p<=1}=ZZ_p $

  The equality between this metric description and the inverse-limit ring
  $varprojlim(n) ZZ slash p^n ZZ$ will be explained by the DVR comparison at
  the end of the chapter.
]

#example(title: "Laurent Series")[
  For the $t$-adic absolute value on $k(t)$, the completion is the
  Laurent-series field

  $ hat(k(t))^(t) tilde.eq k((t)) $

  Indeed, truncating a Laurent series gives rational, in fact
  Laurent-polynomial, approximations whose errors have orders tending to
  infinity.
]

== $p$-adic Fields and Their Rings of Integers

#definition(title: [$p$-adic Field])[
  A #emph[$p$-adic field] is a finite extension

  $ K slash QQ_p $

  The term therefore refers not only to $QQ_p$ itself but to all of its finite
  extensions.
]

#theorem(title: "The Finite-Extension Theorem")[
  Let $K slash QQ_p$ be a finite extension of degree $d$. Then the $p$-adic
  absolute value extends uniquely to $K$. With this absolute value:

  + $K$ is complete;

  + its valuation ring

    $ cal(O)_K:={x in K : abs(x)<=1} $

    is a complete DVR with maximal ideal
    $frak(m)_K={x in K : abs(x)<1}$;

  + the residue field $kappa_K=cal(O)_K slash frak(m)_K$ is finite.

  If $pi$ is a uniformizer, $e=v_K (p)$ and
  $f=[kappa_K:FF_p]$, then

  $ p=u pi^e quad "for some" u in cal(O)_K^times, quad [K:QQ_p]=e f $
]

#proofsketch[
  A finite extension of a complete nonarchimedean field admits a unique
  extension of its absolute value. In the present separable situation it is
  normalized by

  $ abs(x)_K=abs("N"_(K slash QQ_p) (x))_p^(1/d) $

  The integral closure of $ZZ_p$ in $K$ is finite over $ZZ_p$ and is exactly
  the closed unit ball $cal(O)_K$. The uniqueness of the extended valuation
  makes this ring local; being a one-dimensional Noetherian integrally closed
  local domain, it is a DVR. Finite-dimensional normed spaces over the
  complete field $QQ_p$ are complete, so $K$ and the closed subset
  $cal(O)_K$ are complete.

  The residue field is a finite extension of $FF_p$. Finally, multiplication
  by a uniformizer gives a filtration of the free $ZZ_p$-module $cal(O)_K$.
  Comparing its rank with the $e$ successive quotients, each of dimension $f$
  over $FF_p$, yields $d=e f$.
]

The integers $e$ and $f$ are the ramification and residue degrees. They measure
two independent ways in which a $p$-adic field may be larger than $QQ_p$.

=== From a $p$-adic Field to a $p$-adic Ring

#theorem(title: [The Ring of Integers Is a $p$-adic Ring])[
  Let $K$ be a $p$-adic field, with ring of integers $cal(O)_K$, maximal ideal
  $frak(m)_K=(pi)$, and ramification index $e=v_K(p)$. Then:

  + the $p$-adic, $frak(m)_K$-adic, and $pi$-adic topologies on $cal(O)_K$
    coincide;

  + $cal(O)_K$ is a $p$-adic ring, and canonically

    $ cal(O)_K tilde.eq varprojlim(n) cal(O)_K slash p^n cal(O)_K tilde.eq varprojlim(n) cal(O)_K slash frak(m)_K^n $

  + the field is recovered from its ring of integers by

    $ K="Frac"(cal(O)_K)=cal(O)_K [1\/p] $
]

#proof[
  Since $p=u pi^e$ for a unit $u$,

  $ p^n cal(O)_K=frak(m)_K^(e n) $

  The filtrations $(p^n cal(O)_K)$ and $(frak(m)_K^n)$ are cofinal, so they
  define the same topology and the same Cauchy sequences. The ring
  $cal(O)_K$ is the closed unit ball in the complete field $K$, hence is
  complete. It is separated because a nonzero element has finite valuation.
  The equivalent definitions of a $p$-adic ring now give both inverse-limit
  descriptions.

  Every element of $K$ is a quotient of two elements of the DVR
  $cal(O)_K$, so $K="Frac"(cal(O)_K)$. Moreover, for any $x in K$, a
  sufficiently large power of $p$ makes $p^n x$ integral. Hence
  $K=cal(O)_K[1/p]$.
]

#remark(title: "What the Ring Remembers")[
  The field $K$ allows arbitrary powers of the uniformizer in both directions,
  while $cal(O)_K$ keeps only elements of nonnegative valuation. The maximal
  ideal records positive valuation, and the residue field records the leading
  digit. Thus

  $ K supset cal(O)_K supset frak(m)_K supset frak(m)_K^2 supset dots $

  is the algebraic version of successively increasing $p$-adic precision.
]

=== The Converse

#theorem(title: [Recovering a $p$-adic Field from a DVR])[
  Let $A$ be a $p$-adic ring that is also a DVR of mixed characteristic
  $(0,p)$, and suppose its residue field is finite. Then

  $ K:="Frac"(A) $

  is a $p$-adic field, and $A=cal(O)_K$.
]

#proof[
  Let $pi$ be a uniformizer. Since the residue characteristic is $p$, one has

  $ p=u pi^e $

  for some unit $u$ and integer $e>=1$. Thus the $p$-adic and $pi$-adic
  topologies on $A$ coincide. The normalized absolute value

  $ abs(x):=p^(-v_pi (x)\/e) $

  on $K$ restricts to the usual $p$-adic absolute value on $QQ$.

  The field $K$ is complete. Indeed, a Cauchy sequence in $K$ has valuations
  bounded below. Multiplying it by a fixed power of $pi$ produces a Cauchy
  sequence in $A$, which converges because $A$ is complete; division by the
  same power of $pi$ gives the required limit in $K$.

  By the universal property of completion, $QQ->K$ extends to an isometric
  embedding $QQ_p->K$. It remains to prove that $K$ is finite over $QQ_p$.
  The universal property of the ring completion likewise extends $ZZ->A$ to
  $ZZ_p->A$. The quotient $A slash p A=A slash pi^e A$ is finite. Choose
  $b_1,dots,b_r in A$ whose residue classes span it over $FF_p$. Successive
  approximation modulo $p,p^2,dots$ writes every $a in A$ as

  $ a=sum_(i=1)^r lambda_i b_i, quad lambda_i in ZZ_p $

  because the error after the $n$th step lies in $p^n A$ and tends to zero.
  Hence $A$ is a finite $ZZ_p$-module and $K$ is finite-dimensional over
  $QQ_p$. Finally, the nonnegative-valuation elements of $K="Frac"(A)$ are
  exactly $A$, so $A=cal(O)_K$.
]

#corollary(title: [Intrinsic Characterization of $p$-adic Fields])[
  For a field $K$, the following are equivalent.

  + The field $K$ is a finite extension of $QQ_p$.

  + The field $K$ is a complete discretely valued field of characteristic zero
    whose residue field is finite of characteristic $p$.
]

#proof[
  The forward implication is the finite-extension theorem. For the converse,
  the valuation ring $cal(O)_K$ is a complete DVR. Since
  $p cal(O)_K=frak(m)_K^e$, completeness for the valuation topology is the same
  as $p$-adic completeness. The preceding theorem applied to $cal(O)_K$ shows
  that $K$ is finite over $QQ_p$.
]

== Where the Two Completions Meet

The relation is not peculiar to $ZZ$ and $QQ$. It is a general feature of
discrete valuation rings.

#theorem(title: "Completion of a DVR and Its Fraction Field")[
  Let $A$ be a DVR with maximal ideal $frak(m)=(pi)$ and fraction field $K$.
  Equip $K$ with the absolute value

  $ abs(x)=c^(v_pi (x)), quad 0<c<1 $

  Let $hat(A)$ be the $frak(m)$-adic completion and $hat(K)$ the completion of
  the absolute-valued field $K$. Then the inclusion $A->K$ induces

  $ hat(A) tilde.eq cal(O)_(hat(K)), quad hat(K) tilde.eq "Frac"(hat(A)) $

  where $cal(O)_(hat(K))={x in hat(K):abs(x)<=1}$ is the valuation ring of the
  completed field.
]

#proof[
  A sequence in $A$ is $frak(m)$-adically Cauchy exactly when it is Cauchy for
  $abs(dot)$, since

  $ x-y in frak(m)^n <=> v_pi (x-y)>=n <=> abs(x-y)<=c^n $

  Hence $A->K->hat(K)$ extends to an isometric embedding
  $hat(A)->hat(K)$ whose image lies in the closed unit ball.

  Conversely, let $x in hat(K)$ satisfy $abs(x)<=1$. Choose $a in K$ with
  $abs(x-a)<1$. The ultrametric inequality gives $abs(a)<=1$, so $a in A$.
  Repeating this at arbitrarily small radii shows that $A$ is dense in
  $cal(O)_(hat(K))$. Since both sides are complete, the embedding identifies
  $hat(A)$ with this valuation ring.

  Finally, the value group remains discrete after completion: if $x!=0$,
  choose $a in K$ with $abs(x-a)<abs(x)$; then $abs(a)=abs(x)$. Thus a suitable
  power of $pi$ carries $x$ into $cal(O)_(hat(K))=hat(A)$. Therefore every
  element of $hat(K)$ is a fraction of elements of $hat(A)$, proving the
  second isomorphism.
]

#example(title: "The Basic Bridge")[
  For $A=ZZ_((p))$, $frak(m)=(p)$, and $K=QQ$, the theorem becomes

  $ hat(ZZ_((p)))^((p)) tilde.eq ZZ_p, quad hat(QQ)^(abs(dot)_p) tilde.eq QQ_p, quad "Frac"(ZZ_p)=QQ_p $

  Thus the inverse-limit construction on the ring and the Cauchy-sequence
  construction on the field are two views of the same local arithmetic object.
]

== How to Read $ZZ_p$ and $QQ_p$

The inverse-limit and Cauchy-sequence constructions are canonical, but they
can hide what a $p$-adic number actually looks like. This section develops a
working picture that can be used in computations.

#quote[
  $ZZ_p$ consists of infinite base-$p$ integers; $QQ_p$ is obtained by allowing
  finitely many negative powers of $p$.
]

=== Compatible Residue Tuples

#definition(title: "Inverse-Limit Coordinates")[
  Using the canonical representatives of residue classes, an element of $ZZ_p$
  may be written

  $ x=(x_1,x_2,x_3,dots) $

  where

  $ 0<=x_n<p^n, quad x_(n+1) equiv x_n mod p^n $

  The $n$th coordinate is the approximation $x mod p^n$. Addition and
  multiplication are performed coordinatewise and then reduced modulo $p^n$.
]

#example(title: [Coordinates in $ZZ_7$])[
  The first five coordinates correspond to reduction modulo
  $7,7^2,7^3,7^4,7^5$. Ordinary integers, negative integers, and inverses read
  as follows:

  $ 2 &= (2,2,2,2,2,dots) \
    2002 &= (0,42,287,2002,2002,dots) \
    -2 &= (5,47,341,2399,16805,dots) \
    2^(-1) &= (4,25,172,1201,8404,dots) $

  For example, $2002 mod 7^3=287$, while
  $2 dot 8404 equiv 1 mod 7^5$. The equation $x^2=2$ has two compatible
  solutions:

  $ x=cases(
    (3,10,108,2166,4567,dots),
    (4,39,235,235,12240,dots)
  ) $

  and the unique fifth root reducing to $4$ modulo $7$ begins

  $ root(5,2)=(4,46,95,1124,15530,dots) $

  Each row is verified one finite level at a time. For instance, the entries
  in a square-root row satisfy $x_n^2 equiv 2 mod 7^n$ and are compatible under
  reduction. Completeness turns the entire row into an element of $ZZ_7$.
]

#remark(title: "Coordinates Are Truncations, Not Digits")[
  The tuple $(x_n)$ is cumulative: its $n$th entry already contains the first
  $n$ base-$p$ digits. If

  $ x=a_0+a_1 p+a_2 p^2+dots $

  then

  $ x_n=a_0+a_1 p+dots+a_(n-1) p^(n-1) $

  with $0<=x_n<p^n$. Thus the compatible tuple and the digit expansion are two
  presentations of the same element.
]

=== Digits and Precision

#theorem(title: [$p$-adic Digit Expansions])[
  Every $x in ZZ_p$ has a unique expansion

  $ x=sum_(n=0)^infinity a_n p^n, quad a_n in {0,1,dots,p-1} $

  More generally, every nonzero $x in QQ_p$ has a unique expansion

  $ x=sum_(n=N)^infinity a_n p^n, quad N in ZZ, quad a_N!=0 $

  with the same digit set. The element lies in $ZZ_p$ exactly when $N>=0$.
]

#proof[
  An element of $ZZ_p=varprojlim(n) ZZ slash p^n ZZ$ determines a residue
  $a_0$ modulo $p$. After subtracting $a_0$ and dividing by $p$, repeat to
  obtain $a_1,a_2,dots$. At stage $N$ this gives

  $ x equiv a_0+a_1 p+dots+a_(N-1) p^(N-1) mod p^N $

  so completeness gives the displayed expansion. If two expansions first
  differ at the $n$th digit, their difference has valuation exactly $n$;
  hence the expansion is unique.

  For $x in QQ_p^times$, write $x=p^N u$ with $N=v_p (x)$ and
  $u in ZZ_p^times$. Expanding $u$ gives the second formula. Conversely, a
  series beginning at a finite integer $N$ is $p^N$ times an element of
  $ZZ_p$, hence defines an element of $QQ_p$.
]

#remark(title: "Which Direction Is Infinite?")[
  In an ordinary real base-$p$ expansion, finer precision uses increasingly
  negative powers of $p$. In $ZZ_p$, finer precision uses increasingly
  positive powers:

  $ a_0+a_1 p+a_2 p^2+dots $

  It is therefore helpful to picture a $p$-adic integer as a digit string
  extending indefinitely to the left. A $p$-adic number in $QQ_p$ may have
  digits to the right of the radix point, but only finitely many of them.
]

#definition(title: "Finite Precision Notation")[
  The expression

  $ x=a_0+a_1 p+dots+a_(N-1) p^(N-1)+O(p^N) $

  means

  $ x-(a_0+a_1 p+dots+a_(N-1) p^(N-1)) in p^N ZZ_p $

  or equivalently that $x$ is known modulo $p^N$. The symbol $O(p^N)$ records
  an ideal of possible errors, not one particular unknown number.
]

Addition and multiplication can be performed on truncated expansions with the
usual carrying rules. For $a,b in ZZ_p$,

$ (a+O(p^N))+(b+O(p^N))=a+b+O(p^N) $

and

$ (a+O(p^N))(b+O(p^N))=a b+O(p^N) $

If $a$ is a unit, its inverse modulo $p^N$ determines
$(a+O(p^N))^(-1)$ to the same precision.

=== Reading Algebra from the First Nonzero Digit

#proposition(title: "Valuation, Units, and Ideals")[
  Let $0!=x=sum_(n=0)^infinity a_n p^n in ZZ_p$, and let $r$ be the first index
  for which $a_r!=0$. Then

  $ v_p (x)=r, quad abs(x)_p=p^(-r), quad x=p^r u " with " u in ZZ_p^times $

  Consequently:

  + $x$ is a unit if and only if $a_0!=0$;

  + the unique maximal ideal is $p ZZ_p$;

  + every nonzero ideal of $ZZ_p$ is $p^r ZZ_p$ for a unique $r>=0$.

  In particular, $ZZ_p$ is a complete DVR and
  $ZZ_p slash p ZZ_p tilde.eq FF_p$.
]

#proof[
  Factoring out the first nonzero power gives

  $ x=p^r (a_r+a_(r+1) p+dots) $

  The factor in parentheses has nonzero reduction modulo $p$ and is therefore
  a unit. This proves the valuation and unit statements. If $I$ is a nonzero
  ideal, choose $x in I$ with minimal valuation $r$. Then $(x)=p^r ZZ_p$, and
  every element of $I$ has valuation at least $r$, so

  $ p^r ZZ_p=(x) subset.eq I subset.eq p^r ZZ_p $

  This proves the classification of ideals.
]

#remark(title: "A Quick Reading Rule")[
  Initial zero digits measure divisibility. If a number begins with $r$ zeros
  before its first nonzero digit, it lies in $p^r ZZ_p$ and has absolute value
  $p^(-r)$. Thus a long initial string of zeros makes a number
  #emph[small], the reverse of the usual real intuition about large powers of
  $p$.
]

=== Residue Classes as Balls

For $a in ZZ_p$ and $N>=0$,

$ a+p^N ZZ_p={x in ZZ_p : abs(x-a)_p<=p^(-N)} $

Thus knowing the first $N$ digits is the same as knowing a closed ball. In the
ultrametric topology this ball is also open. It splits into $p$ disjoint balls
of the next precision:

$ a+p^N ZZ_p=union.big_(b=0)^(p-1) (a+b p^N+p^(N+1) ZZ_p) $

#remark(title: [The $p$-ary Tree])[
  Start with $ZZ_p$. Reduction modulo $p$ splits it into $p$ balls. Each of
  those splits into $p$ residue classes modulo $p^2$, and the process
  continues. An element of $ZZ_p$ is an infinite path down this rooted
  $p$-ary tree. Two paths are close precisely when they share a long initial
  segment.
]

Because every level $ZZ slash p^N ZZ$ is finite,
$ZZ_p=varprojlim(N) ZZ slash p^N ZZ$ is compact and totally disconnected. The
field $QQ_p$ is not compact, but it is locally compact because $ZZ_p$ is a
compact open neighborhood of $0$.

=== Passing from $ZZ_p$ to $QQ_p$

The equality

$ QQ_p="Frac"(ZZ_p)=ZZ_p [1\/p]=union.big_(N>=0) p^(-N) ZZ_p $

says that $QQ_p$ introduces no new infinite tails: it only permits the digit
expansion to begin at a negative exponent. Every nonzero element still has a
unique valuation--unit decomposition

$ x=p^(v_p (x)) u, quad u in ZZ_p^times $

The integer $v_p(x)$ gives the scale and the unit $u$ contains the digit data.
Elements of negative valuation are $p$-adically large; for example,
$abs(p^(-100))_p=p^100$.

#example(title: "Negative Integers Have Infinite Tails")[
  Since $p^N->0$ in $ZZ_p$,

  $ -1=(p-1)+(p-1)p+(p-1)p^2+dots $

  Indeed, the partial sum through degree $N-1$ is $p^N-1$, which tends to
  $-1$. For $p=2$, this is the memorable identity

  $ -1=1+2+2^2+2^3+dots $

  Thus an infinite string of base-$2$ digits $dots 1111$ represents $-1$ in
  $ZZ_2$.
]

#example(title: "Geometric Series")[
  The usual finite identity

  $ (1-p)(1+p+dots+p^N)=1-p^(N+1) $

  has a $p$-adic limit because $p^(N+1)->0$. Therefore

  $ sum_(n=0)^infinity p^n=1/(1-p) $

  For $p=2$, the right-hand side is $-1$, recovering the preceding digit
  expansion. This is the basic reading principle for $p$-adic analysis: a
  series converges when its terms become increasingly divisible by $p$.
]
