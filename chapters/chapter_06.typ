#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Valuations and Absolute Values

Chapter 1 used discrete valuations to describe DVRs and orders of vanishing.
We now remove the discreteness assumption. The value of an element may lie in
an arbitrary totally ordered abelian group, so several scales of smallness can
coexist and the value group may even be dense. Absolute values are the
real-valued, multiplicative counterpart of this theory; they turn arithmetic
size into a topology, placing ordinary and nonarchimedean analysis in a common
framework.

== General Valuations

=== Ordered Value Groups

#definition(title: "Totally Ordered Abelian Group")[
  A #emph[totally ordered abelian group] is an abelian group $Gamma$, written
  additively, equipped with a total order such that

  $ gamma<=delta => gamma+eta<=delta+eta $

  for all $gamma,delta,eta in Gamma$. We adjoin an element $+infinity$ with

  $ gamma<+infinity, quad gamma+(+infinity)=+infinity $

  and write $Gamma_infinity=Gamma union {+infinity}$.
]

The familiar value group $ZZ$ has one smallest positive element. This need
not happen in general: $QQ$ and $RR$ have no smallest positive element, and
$ZZ^2$ with the lexicographic order has two visibly different scales.

#definition(title: "Valuation")[
  Let $K$ be a field and $Gamma$ a totally ordered abelian group. A
  #emph[valuation] on $K$ with values in $Gamma$ is a map

  $ v:K->Gamma_infinity $

  satisfying, for all $x,y in K$,

  + $v(x)=+infinity$ if and only if $x=0$;

  + $v(x y)=v(x)+v(y)$;

  + $v(x+y)>=min(v(x),v(y))$.

  Its #emph[value group] is the ordered subgroup

  $ Gamma_v:=v(K^times) subset.eq Gamma $

  The valuation is #emph[trivial] if $Gamma_v={0}$. Since replacing $Gamma$
  by $Gamma_v$ loses no information, one often assumes that
  $v:K^times->Gamma$ is surjective.
]

#remark(title: "Additive Convention")[
  We use additive valuations: a larger value means a smaller or more
  divisible element. Thus zeros have positive value, poles have negative
  value, and $v(0)=+infinity$. This is the convention already used for DVRs
  in Chapter 1.
]

#proposition(title: "Valuation Calculus")[
  Let $v$ be a valuation on $K$. For $x,y in K^times$,

  $ v(1)=v(-1)=0, quad v(x^(-1))=-v(x), quad v(x slash y)=v(x)-v(y) $

  If $v(x)!=v(y)$, then the ultrametric inequality is an equality:

  $ v(x+y)=min(v(x),v(y)) $

  More generally,

  $ v(x_1+dots+x_n)>=min_i v(x_i) $

  and if the minimum occurs exactly once, the sum is nonzero and equality
  holds.
]

#proof[
  Multiplicativity gives

  $ v(1)=v(1^2)=2v(1) $

  so $v(1)=0$. Since $(-1)^2=1$, one has $2v(-1)=0$; an ordered abelian group
  is torsion-free, hence $v(-1)=0$. The inverse and quotient formulas follow
  from $v(x x^(-1))=0$.

  Suppose, after exchanging $x$ and $y$, that $v(x)<v(y)$. The valuation
  inequality gives $v(x+y)>=v(x)$. If this inequality were strict, then

  $ v(x)=v((x+y)-y)>=min(v(x+y),v(y))>v(x) $

  a contradiction. Hence $v(x+y)=v(x)$. The finite-sum inequality follows by
  induction. If one term has uniquely least value, combine all the other
  terms first and apply the two-term equality.
]

#remark(title: "Cancellation Can Only Increase Value")[
  The inequality may be strict only when the terms of least value cancel. For
  example, $v_p(1)=v_p(-1)=0$ but $v_p(1+(-1))=+infinity$. This simple fact is
  the source of much of nonarchimedean rigidity: unequal sizes cannot cancel.
]

=== Valuation Rings

#definition(title: "Valuation Ring, Maximal Ideal, and Residue Field")[
  The #emph[valuation ring] and its positive-value ideal are

  $ cal(O)_v:={x in K | v(x)>=0}, quad frak(m)_v:={x in K | v(x)>0} $

  The #emph[residue field] of $v$ is

  $ kappa(v):=cal(O)_v slash frak(m)_v $
]

#theorem(title: "Basic Structure of a Valuation Ring")[
  The set $cal(O)_v$ is a local domain with fraction field $K$, unique maximal
  ideal $frak(m)_v$, and unit group

  $ cal(O)_v^times={x in K | v(x)=0} $

  For every $x in K^times$, either $x in cal(O)_v$ or
  $x^(-1) in cal(O)_v$. Moreover, the ideals of $cal(O)_v$ are totally
  ordered by inclusion, every finitely generated ideal is principal, and
  $cal(O)_v$ is integrally closed in $K$.
]

#proof[
  If $v(x),v(y)>=0$, then
  $v(x+y)>=0$ and $v(x y)>=0$, so $cal(O)_v$ is a subring of $K$. For
  $x in K^times$, either $v(x)>=0$ or $v(x)<0$, in which case
  $v(x^(-1))>0$. Thus every element of $K$ is a quotient of elements of
  $cal(O)_v$.

  An element $x in cal(O)_v$ is a unit exactly when
  $x^(-1) in cal(O)_v$, equivalently $v(x)=0$. Hence the nonunits are exactly
  the elements of $frak(m)_v$, proving that this is the unique maximal ideal.

  Let $I,J$ be ideals that are not comparable. Choose
  $x in I without J$ and $y in J without I$. Either $v(x)<=v(y)$, in which
  case $y slash x in cal(O)_v$ and $y in (x) subset.eq I$, or
  $v(y)<=v(x)$, in which case $x in (y) subset.eq J$. Both alternatives are
  contradictions. Thus all ideals are comparable. Among finitely many
  generators, choose one of least value; it generates all the others and
  hence the entire ideal.

  Finally, suppose $z in K$ is integral over $cal(O)_v$ and $v(z)<0$. In a
  monic relation

  $ z^n+a_(n-1)z^(n-1)+dots+a_0=0 $

  with $a_i in cal(O)_v$, the leading term has value $n v(z)$, strictly less
  than the value of every other term. The unique-minimum property makes such
  a sum nonzero, a contradiction. Thus $v(z)>=0$ and $z in cal(O)_v$.
]

#corollary(title: "Divisibility Is Measured by Value")[
  For nonzero $x,y in K$,

  $ x cal(O)_v subset.eq y cal(O)_v <=> v(x)>=v(y) $

  and

  $ x " divides " y " in " cal(O)_v <=> v(x)<=v(y) $
]

#proof[
  The inclusion $x cal(O)_v subset.eq y cal(O)_v$ holds exactly when
  $x slash y in cal(O)_v$, which is equivalent to $v(x)-v(y)>=0$. The second
  assertion is the same statement with $x$ and $y$ interchanged.
]

#theorem(title: "Intrinsic Characterizations of Valuation Rings")[
  Let $R$ be a domain with fraction field $K$. The following conditions are
  equivalent.

  + There is a valuation $v$ on $K$ with $R=cal(O)_v$.

  + For every $x in K^times$, either $x in R$ or $x^(-1) in R$.

  + The principal ideals of $R$ are totally ordered by inclusion.

  + All ideals of $R$ are totally ordered by inclusion.
]

#proof[
  The preceding theorem proves the first condition implies the second and
  fourth, and the fourth clearly implies the third.

  Suppose principal ideals are totally ordered. Write $x=a slash b$ with
  $a,b in R$ nonzero. Either $(a) subset.eq (b)$, which gives $x in R$, or
  $(b) subset.eq (a)$, which gives $x^(-1) in R$. Thus the third condition
  implies the second.

  Now assume the second condition. Put

  $ Gamma:=K^times slash R^times $

  and define an order by

  $ [x]<=[y] <=> y slash x in R $

  This is well defined, translation invariant, and total because either
  $y slash x$ or $x slash y$ belongs to $R$. The quotient map

  $ v:K^times->Gamma, quad x mapsto [x] $

  is a group homomorphism. If $v(x)<=v(y)$, then $y slash x in R$, so

  $ (x+y) slash x=1+y slash x in R $

  and therefore $v(x+y)>=v(x)$. This proves the valuation inequality; extend
  by $v(0)=+infinity$. Finally,

  $ v(x)>=0 <=> x in R $

  so $R=cal(O)_v$.
]

#remark(title: "DVRs among Valuation Rings")[
  A valuation ring need not be Noetherian and its maximal ideal need not be
  principal. Chapter 1 shows that a nonfield valuation ring is Noetherian
  exactly when it is a DVR; after normalization its value group is $ZZ$.
  Thus DVRs are precisely the discrete, one-scale members of the much larger
  world of valuation rings.
]

=== Equivalent Valuations

#definition(title: "Equivalence of Valuations")[
  Two valuations $v$ and $w$ on $K$ are #emph[equivalent] if there is an
  order-preserving group isomorphism

  $ phi:Gamma_v tilde.eq Gamma_w $

  such that $w=phi compose v$ on $K^times$.
]

#theorem(title: "A Valuation Is Determined by Its Ring")[
  Two valuations $v,w$ on $K$ are equivalent if and only if

  $ cal(O)_v=cal(O)_w $
]

#proof[
  Equivalent valuations clearly have the same nonnegative elements and hence
  the same valuation ring.

  Conversely, suppose $cal(O)_v=cal(O)_w$. Define

  $ phi:Gamma_v->Gamma_w, quad v(x) mapsto w(x) $

  If $v(x)=v(y)$, then $x slash y$ has value zero and is a unit of
  $cal(O)_v$. The two valuation rings have the same units, so
  $w(x slash y)=0$ and $w(x)=w(y)$. Thus $phi$ is well defined; symmetry
  gives bijectivity, and multiplicativity gives additivity. Finally,

  $ v(x)<=v(y) <=> y slash x in cal(O)_v <=> y slash x in cal(O)_w <=> w(x)<=w(y) $

  so $phi$ preserves and reflects the order.
]

#remark(title: "What the Equivalence Class Remembers")[
  A valuation can be rescaled or have its value group renamed without
  changing divisibility. The valuation ring, maximal ideal, residue field,
  and induced topology depend only on the equivalence class.
]

=== Examples beyond the Discrete Case

#example(title: "Trivial and Discrete Valuations")[
  The trivial valuation has $v(x)=0$ for every $x!=0$ and valuation ring $K$.
  The familiar valuations $v_p$ on $QQ$, $"ord"_t$ on $k(t)$, and the order of
  vanishing along a prime divisor are discrete valuations with value group
  $ZZ$.
]

#example(title: "A Dense Value Group")[
  Fix an irrational real number $alpha>0$. For a nonzero polynomial

  $ f=sum_(i,j) a_(i j)x^i y^j in k[x,y] $

  put

  $ v_alpha (f):=min{ i+alpha j | a_(i j)!=0 } $

  and extend to $k(x,y)$ by

  $ v_alpha (f slash g)=v_alpha (f)-v_alpha (g) $

  Irrationality makes the lowest-weight monomial unique, so lowest terms
  cannot cancel in a product and
  $v_alpha (f g)=v_alpha (f)+v_alpha (g)$. The value group is
  $ZZ+alpha ZZ subset.eq RR$, which is dense in $RR$. There is no smallest
  positive value, so the maximal ideal of $cal(O)_(v_alpha)$ is not principal
  and the ring is not Noetherian.
]

#example(title: "A Rank-Two Valuation")[
  Let $K=k((u))((t))$. Every nonzero element has an expansion

  $ f=sum_(n>=n_0) a_n (u)t^n, quad a_(n_0)(u)!=0 $

  Define

  $ v(f):=(n_0,"ord"_u (a_(n_0))) in ZZ^2_"lex" $

  where $ZZ^2_"lex"$ is ordered lexicographically. The first coordinate
  measures the $t$-adic scale, and only when it ties does the second coordinate
  inspect the $u$-adic scale. This is a genuinely higher-rank valuation: no
  embedding of its ordered value group into $RR$ can preserve the
  lexicographic order.
]

#example(title: "Divisorial Valuations")[
  Let $X$ be a normal integral variety with function field $K$, and let $D$ be
  a prime divisor. The local ring $cal(O)_(X,D)$ is a DVR, and

  $ "ord"_D:K^times->ZZ $

  measures the order of vanishing along $D$. This is the geometric source of
  the valuations used in Weil divisors. More general valuations behave like
  orders of vanishing along increasingly infinitesimal or higher-rank
  directions, even when no single divisor represents them.
]

=== Valuation Topology and Centers

For $gamma in Gamma_v$ and $a in K$, put

$ U_gamma (a):={x in K | v(x-a)>gamma} $

These sets form a neighborhood basis and define the #emph[valuation topology]
on $K$. Addition, multiplication, and inversion on $K^times$ are continuous.
Equivalent valuations give exactly the same topology.

#remark(title: "General Valuations Need Not Be Metrizable")[
  A valuation topology is controlled by the ordered group $Gamma_v$. If this
  group has no countable cofinal family of positive values, the topology need
  not be first countable and therefore need not arise from a metric. Absolute
  values select the particularly useful case in which size is measured by
  positive real numbers.
]

#remark(title: "The Geometric Center of a Valuation")[
  Let $X$ be an integral scheme with function field $K$. A valuation ring
  $cal(O)_v subset.eq K$ has a #emph[center] $x in X$ if

  $ cal(O)_(X,x) subset.eq cal(O)_v, quad frak(m)_v inter cal(O)_(X,x)=frak(m)_x $

  Equivalently, the generic-point map extends to a commutative diagram

  $ "Spec" K -> "Spec" cal(O)_v -> X $

  with the closed point mapping to $x$. A DVR gives a generic point together
  with one specialization; a higher-rank valuation records a longer chain of
  specializations. The valuative criterion for properness says, in
  particular, that valuations centered on the generic point cannot escape a
  proper model.
]

== Absolute Values

=== Definitions and First Examples

#definition(title: "Absolute Value")[
  An #emph[absolute value] on a field $K$ is a map

  $ abs(dot):K->RR_(>=0) $

  such that, for all $x,y in K$,

  + $abs(x)=0$ if and only if $x=0$;

  + $abs(x y)=abs(x)abs(y)$;

  + $abs(x+y)<=abs(x)+abs(y)$.

  It is #emph[trivial] if $abs(x)=1$ for every $x in K^times$.
]

As with valuations,

$ abs(1)=abs(-1)=1, quad abs(x^(-1))=abs(x)^(-1), quad abs(x slash y)=abs(x) slash abs(y) $

The basic examples on $QQ$ are the usual absolute value $abs(dot)_infinity$
and, for each prime $p$, the #emph[$p$-adic absolute value]

$ abs(x)_p:=p^(-v_p (x)), quad abs(0)_p:=0 $

The first measures ordinary magnitude; the second declares a number small
when it is divisible by a large power of $p$.

#remark(title: "Analogy with Normed Spaces")[
  An absolute value on $K$ measures the size of #emph[scalars], just as a norm
  measures the size of #emph[vectors]. More precisely, a norm on a
  $K$-vector space $V$ is a map

  $ norm(dot):V->RR_(>=0) $

  satisfying $norm(a x)=abs(a)norm(x)$ and
  $norm(x+y)<=norm(x)+norm(y)$, together with $norm(x)=0 <=> x=0$. Thus an
  absolute-valued field is the one-dimensional case $V=K$, and
  $d(x,y)=norm(x-y)$ produces its metric and topology. In the
  nonarchimedean setting the analogous norm satisfies
  $norm(x+y)<=max(norm(x),norm(y))$; this is the starting point for
  nonarchimedean normed spaces.
]

#definition(title: "Archimedean and Nonarchimedean Absolute Values")[
  An absolute value is #emph[nonarchimedean] if it satisfies the stronger
  triangle inequality

  $ abs(x+y)<=max(abs(x),abs(y)) $

  It is #emph[archimedean] otherwise. The strong inequality is also called
  the #emph[ultrametric inequality].
]

The usual absolute value is archimedean, while the trivial and $p$-adic
absolute values are nonarchimedean.

=== Characterizing the Nonarchimedean Case

#theorem(title: "Equivalent Forms of the Ultrametric Inequality")[
  For an absolute value $abs(dot)$ on $K$, the following conditions are
  equivalent.

  + The absolute value is nonarchimedean.

  + $abs(n)<=1$ for every positive integer $n$ viewed inside $K$.

  + The set ${abs(n) : n in ZZ}$ is bounded in $RR$.
]

#proof[
  The ultrametric inequality gives

  $ abs(n)=abs(1+dots+1)<=1 $

  so the first condition implies the second, and the second implies the
  third.

  Suppose instead that $abs(n)<=C$ for every integer $n$. For a fixed
  positive integer $m$,

  $ abs(m)^r=abs(m^r)<=C $

  for every $r>=1$. Taking $r$th roots and letting $r$ tend to infinity gives
  $abs(m)<=1$, so the third condition implies the second.

  Finally, assume $abs(n)<=1$ for every positive integer $n$ and put
  $M=max(abs(x),abs(y))$. The binomial theorem and the ordinary triangle
  inequality give

  $ abs((x+y)^n)<=sum_(j=0)^n abs(binom(n,j)) abs(x)^j abs(y)^(n-j)<=(n+1)M^n $

  Hence

  $ abs(x+y)<=(n+1)^(1/n) M $

  Letting $n$ tend to infinity yields the ultrametric inequality.
]

#proposition(title: "Rigid Triangles")[
  For a nonarchimedean absolute value, if $abs(x)!=abs(y)$, then

  $ abs(x+y)=max(abs(x),abs(y)) $

  Thus every triangle is isosceles with its two longer sides equal.
]

#proof[
  Suppose $abs(x)<abs(y)$. The strong triangle inequality gives
  $abs(x+y)<=abs(y)$. On the other hand,

  $ abs(y)=abs((x+y)-x)<=max(abs(x+y),abs(x)) $

  and the strict inequality $abs(x)<abs(y)$ forces
  $abs(y)<=abs(x+y)$. Therefore equality holds.
]

=== From Valuations to Absolute Values

#theorem(title: [The Additive--Multiplicative Dictionary])[
  Let $v:K^times->Gamma_v$ be a valuation whose value group is an ordered
  subgroup of $RR$, and choose $0<c<1$. Then

  $ abs(x)_v:=cases(
    0 quad & x=0,
    c^(v(x)) quad & x!=0
  ) $

  is a nonarchimedean absolute value.

  Conversely, if $abs(dot)$ is a nonarchimedean absolute value, then

  $ v_(abs(dot)) (x):=-log(abs(x)) $

  defines an $RR$-valued valuation on $K^times$. These constructions recover
  one another after the harmless choice of scale. Under this dictionary,

  $ cal(O)_v={x in K : abs(x)_v<=1}, quad frak(m)_v={x in K : abs(x)_v<1} $
]

#proof[
  Multiplicativity follows from
  $c^(v(x y))=c^(v(x)+v(y))$. Since $0<c<1$, reversing the valuation
  inequality gives

  $ c^(v(x+y))<=c^(min(v(x),v(y)))=max(c^(v(x)),c^(v(y))) $

  so $abs(dot)_v$ is nonarchimedean.

  Conversely, logarithms convert products into sums, and

  $ abs(x+y)<=max(abs(x),abs(y)) $

  becomes

  $ -log(abs(x+y))>=min(-log(abs(x)),-log(abs(y))) $

  The descriptions of $cal(O)_v$ and $frak(m)_v$ follow because $c^r<=1$
  exactly when $r>=0$.
]

#remark(title: "Not Every Valuation Is an Absolute Value")[
  The construction requires an order-preserving embedding of the value group
  into $RR$. Dense subgroups such as $ZZ+alpha ZZ$ cause no problem, but the
  lexicographically ordered group $ZZ^2_"lex"$ cannot embed in $RR$ as an
  ordered group. General valuations therefore contain genuinely more
  information than real-valued absolute values.
]

=== Equivalent Absolute Values

#definition(title: "Equivalence of Absolute Values")[
  Two nontrivial absolute values $abs(dot)_1$ and $abs(dot)_2$ on $K$ are
  #emph[equivalent] if there exists a real number $s>0$ such that

  $ abs(x)_2=abs(x)_1^s $

  for every $x in K$.
]

#theorem(title: "Topology Determines an Absolute Value up to Scale")[
  Two nontrivial absolute values on $K$ are equivalent if and only if they
  induce the same topology.
]

#proof[
  Positive powers clearly produce the same open balls and hence the same
  topology.

  Conversely, suppose the two topologies agree. For every $x in K$,

  $ abs(x)_1<1 <=> x^n->0 <=> abs(x)_2<1 $

  Choose $a in K^times$ with $abs(a)_1<1$; the same then holds for
  $abs(a)_2$. Put

  $ lambda_i(x):=-log(abs(x)_i) $

  For positive integers $m,n$, equality of the two notions of smallness gives

  $ m lambda_1(x)-n lambda_1(a)>0 <=> m lambda_2(x)-n lambda_2(a)>0 $

  Indeed, each inequality says that $abs(x^m a^(-n))_i<1$. As $n slash m$
  ranges over the positive rationals, these identical rational cuts imply

  $ lambda_2(x) slash lambda_2(a)=lambda_1(x) slash lambda_1(a) $

  first for $abs(x)_1<1$, then for all $x$ by taking inverses and including
  the case $abs(x)_1=1$. Thus $lambda_2=s lambda_1$ for the positive constant
  $s=lambda_2(a) slash lambda_1(a)$, which is equivalent to
  $abs(x)_2=abs(x)_1^s$.
]

#remark(title: "Normalization and Equivalent Norms")[
  Equivalent absolute values define the same topology, convergent sequences,
  and valuation ring in the nonarchimedean case. A normalization such as
  $abs(p)_p=p^(-1)$ merely fixes a convenient unit of measurement. This
  parallels #emph[equivalent norms] in functional analysis: two norms on a
  vector space define the same topology when, for some $C>=1$,

  $ C^(-1) norm(x)_1<=norm(x)_2<=C norm(x)_1 $

  Absolute values are more rigid: multiplicativity upgrades such topological
  equivalence to the exact power relation $abs(x)_2=abs(x)_1^s$.
]

== Ostrowski's Theorem for $QQ$

#theorem(title: [Classification of Absolute Values on $QQ$])[
  Every nontrivial absolute value on $QQ$ is equivalent to exactly one of

  + the usual absolute value $abs(dot)_infinity$;

  + the $p$-adic absolute value $abs(dot)_p$ for a unique prime $p$.
]

#proof[
  Suppose first that the absolute value is nonarchimedean. Then
  $abs(n)<=1$ for every integer $n$. Since it is nontrivial, some prime $p$
  satisfies $abs(p)<1$. There cannot be two such primes: if
  $abs(p),abs(q)<1$ with $p!=q$, choose integers $a,b$ with $a p+b q=1$.
  The ultrametric inequality would give

  $ 1<=max(abs(a)abs(p),abs(b)abs(q))<1 $

  a contradiction. Thus $abs(q)=1$ for every prime $q!=p$. Writing a rational
  number as $x=p^n a slash b$ with $p$ dividing neither $a$ nor $b$ gives

  $ abs(x)=abs(p)^n $

  If $s=-log(abs(p)) slash log(p)>0$, then

  $ abs(x)=abs(x)_p^s $

  so the absolute value is equivalent to the $p$-adic one.

  Now suppose the absolute value is archimedean. The integer values are
  unbounded, so choose an integer $b>1$ with $abs(b)>1$. In fact
  $abs(a)>1$ for every integer $a>1$: otherwise, writing $b^n$ in base $a$
  and applying the triangle inequality would bound $abs(b)^n$ by a quantity
  growing only linearly in $n$, which is impossible.

  Write $a^n$ in base $b$. It uses at most
  $n log(a) slash log(b)+1$ digits, each chosen from a fixed finite set. If
  $C_b=max_{0<=j<b} abs(j)$, the triangle inequality gives

  $ abs(a)^n<=C_b (n log(a) slash log(b)+2) abs(b)^(n log(a) slash log(b)+1) $

  Taking $n$th roots and letting $n$ tend to infinity yields

  $ log(abs(a)) slash log(a)<=log(abs(b)) slash log(b) $

  Exchanging $a$ and $b$ proves equality. Hence there is a constant $s>0$
  such that $abs(n)=n^s$ for every positive integer $n$, and multiplicativity
  extends this to $abs(x)=abs(x)_infinity^s$ for every $x in QQ$. The two
  types are inequivalent because one is archimedean and the other is not, and
  distinct primes give different elements of absolute value less than one.
]

#remark(title: "Why This Classification Matters")[
  Up to equivalence, $QQ$ has one ordinary notion of size and one
  nonarchimedean notion for each prime. The archimedean and prime-adic worlds
  are therefore not arbitrary additions: they exhaust all possible notions of
  size on $QQ$.
]

== Ultrametric Topology and Analysis

Every absolute value defines a translation-invariant metric

$ d(x,y):=abs(x-y) $

For $a in K$ and $r>0$, write

$ B(a,r):={x in K : abs(x-a)<r} $

#remark(title: "The Normed-Space Dictionary")[
  Viewed as a one-dimensional normed space over itself, $K$ has
  $norm(x)=abs(x)$ and $d(x,y)=norm(x-y)$. Thus open balls, convergence, Cauchy
  sequences, continuity, and completeness are defined exactly as in ordinary
  normed spaces. The new feature is not the language of topology but the
  ultrametric geometry forced by the strong triangle inequality.
]

=== Ultrametric Balls

#proposition(title: "Geometry of Ultrametric Balls")[
  Suppose $K$ is nonarchimedean.

  + Every point of a ball is a center: if $b in B(a,r)$, then
    $B(a,r)=B(b,r)$.

  + Two balls are either disjoint or one contains the other.

  + Every open ball is also closed.
]

#proof[
  If $b in B(a,r)$, then for any $x$,

  $ abs(x-b)<=max(abs(x-a),abs(a-b)) $

  so $x in B(a,r)$ implies $x in B(b,r)$; symmetry gives equality.

  Suppose $B(a,r)$ and $B(b,s)$ meet and $r<=s$. Choose $z$ in their
  intersection. Then $abs(a-b)<s$. For $x in B(a,r)$,

  $ abs(x-b)<=max(abs(x-a),abs(a-b))<s $

  so $B(a,r) subset.eq B(b,s)$.

  Finally, if $y in.not B(a,r)$ and $abs(z-y)<abs(y-a)$, the rigid-triangle
  property gives $abs(z-a)=abs(y-a)>=r$. Thus a neighborhood of every point
  in the complement remains in the complement, so the ball is closed.
]

=== Cauchy Sequences and Series

#definition(title: "Cauchy Sequences and Completeness")[
  A sequence $(x_n)$ in a valued field is #emph[Cauchy] if for every
  $epsilon>0$ there exists $N$ such that

  $ m,n>=N => abs(x_m-x_n)<epsilon $

  The field is #emph[complete] if every Cauchy sequence converges. In the
  normed-space analogy, a complete valued field plays the role of the scalar
  field underlying a Banach space.
]

#proposition(title: "Convergence of Nonarchimedean Series")[
  Let $K$ be complete for a nonarchimedean absolute value. A series

  $ sum_(n=0)^infinity a_n $

  converges if and only if $a_n->0$.
]

#proof[
  Convergence always forces the terms to tend to zero. Conversely, if
  $a_n->0$, then for $m<=n$,

  $ abs(sum_(j=m)^n a_j)<=max_(m<=j<=n) abs(a_j) $

  The right-hand side tends to zero with $m$, so the partial sums form a
  Cauchy sequence and converge by completeness.
]

#remark(title: "No Accumulation of Small Errors")[
  Over $RR$, convergence of a series requires control of the accumulated sum
  of its terms. In an ultrametric field, a finite sum is no larger than its
  largest term. Once individual errors become small, their total cannot grow
  again. This is why iterative methods such as Hensel lifting converge so
  efficiently.
]

== Topological Fields

#definition(title: "Topological Field and Absolute-Valued Field")[
  A #emph[topological field] is a field $K$ equipped with a Hausdorff topology
  for which addition and multiplication

  $ K times K->K $

  and inversion $K^times->K^times$ are continuous. An
  #emph[absolute-valued field] is a pair $(K,abs(dot))$ consisting of a field
  and an absolute value; it is always equipped with the metric topology
  induced by

  $ d(x,y)=abs(x-y) $
]

#proposition(title: "An Absolute Value Defines a Topological Field")[
  The metric topology of every absolute-valued field makes $K$ a topological
  field. The balls $B(0,r)$ form a neighborhood basis at $0$, and every map

  $ x mapsto a x+b, quad a in K^times, b in K $

  is a homeomorphism.
]

#proof[
  The metric is Hausdorff. Continuity of the field operations follows from

  $ abs((x+y)-(x'+y'))<=abs(x-x')+abs(y-y') $

  and

  $ abs(x y-x' y')<=abs(x)abs(y-y')+abs(y')abs(x-x') $

  For $x,y!=0$,

  $ abs(x^(-1)-y^(-1))=abs(x-y) slash (abs(x)abs(y)) $

  As $y->x!=0$, the value $abs(y)$ stays bounded away from zero, which proves
  continuity of inversion. Translations and multiplication by a nonzero scalar
  are continuous and have continuous inverses, so they are homeomorphisms; in
  particular, neighborhoods of $0$ determine the entire topology.
]

#theorem(title: "Comparing Absolute-Value Topologies")[
  Let $tau_1,tau_2$ be the topologies on $K$ induced by absolute values
  $abs(dot)_1,abs(dot)_2$.

  + If both absolute values are nontrivial, then $tau_1=tau_2$ if and only if
    $abs(x)_2=abs(x)_1^s$ for some $s>0$ and every $x in K$.

  + Two distinct topologies induced by nontrivial absolute values are
    incomparable: neither is finer than the other.

  + The trivial absolute value induces the discrete topology, which is finer
    than every nontrivial absolute-value topology.
]

#proof[
  The first statement is the theorem #emph[Topology Determines an Absolute
  Value up to Scale] above. For the second, suppose for example that $tau_1$
  is finer than $tau_2$. Then the identity map from $(K,tau_1)$ to
  $(K,tau_2)$ is continuous. Hence

  $ abs(x)_1<1 => x^n->0 " in " tau_1 => x^n->0 " in " tau_2 => abs(x)_2<1 $

  Choose $a$ with $abs(a)_1<1$; then also $abs(a)_2<1$. If
  $abs(x)_2<1$ but $abs(x)_1>=1$, fix $m>=1$ and choose $n$ sufficiently
  large. The element $y=a^m x^(-n)$ then satisfies

  $ abs(y)_1<1 quad "but" quad abs(y)_2>1 $

  contradicting the displayed implication. Thus
  $abs(x)_1<1 <=> abs(x)_2<1$. The proof of the first statement now gives a
  power relation, so $tau_1=tau_2$. Therefore no strict comparison is possible
  between two nontrivial absolute-value topologies.

  Finally, for the trivial absolute value, $B(0,r)={0}$ whenever $0<r<=1$.
  Every singleton is therefore open, so its topology is discrete.
]
