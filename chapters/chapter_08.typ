#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Local Fields

The preceding chapters constructed completions and explained how to read
$ZZ_p$ and $QQ_p$. We now isolate the topological property that makes these
completed fields genuinely manageable. A local field is not merely complete:
it is locally compact, so bounded arithmetic data cannot escape without
leaving a convergent subsequence.

#quote[
  A local field is what remains of a global field after we focus on one place
  and complete there.
]

== Definition and the Nonarchimedean Criterion

=== Compact Neighborhoods and Balls

#definition(title: "Local Compactness")[
  A Hausdorff topological space $X$ is #emph[locally compact] if every point of
  $X$ has a compact neighborhood. For a metric space, this is equivalent to
  requiring every point to lie in some compact closed ball.
]

Let $(K,abs(dot))$ be an absolute-valued field. We use the notation

$ B_(<r) (a):={x in K:abs(x-a)<r}, quad B_(<=r) (a):={x in K:abs(x-a)<=r} $

for its open and closed balls. Translation and multiplication by a nonzero
scalar are homeomorphisms, so the local topology at any one point already
determines the local topology everywhere.

#definition(title: "Local Field")[
  A #emph[local field] is a field $K$ equipped with a #emph[nontrivial]
  absolute value such that the induced metric topology is locally compact.

  Some authors reserve the term local field for the nonarchimedean case. Here
  we follow the convention that also includes $RR$ and $CC$, and explicitly
  say #emph[nonarchimedean local field] when needed.
]

#remark(title: "Why Nontrivial?")[
  The trivial absolute value gives the discrete topology. It would make every
  finite field locally compact and would admit many degenerate examples that
  do not encode a place. Requiring a nontrivial absolute value keeps the
  definition focused on arithmetic completions.
]

#lemma(title: "Compact-Ball Criterion")[
  Let $K$ carry a nontrivial absolute value. The following conditions are
  equivalent.

  + $K$ is a local field.

  + Every closed ball in $K$ is compact.

  + Some closed ball of positive radius in $K$ is compact.
]

#proof[
  If every closed ball is compact, then every point has a compact
  neighborhood, so $K$ is locally compact.

  Conversely, suppose that $K$ is locally compact. A compact neighborhood of
  $0$ contains a closed ball $B_(<=s) (0)$ for some $s>0$. Since the absolute
  value is nontrivial, there is an $alpha in K^times$ with $abs(alpha)>1$.
  Multiplication by $alpha^n$ identifies $B_(<=s) (0)$ with

  $ B_(<=abs(alpha)^n s) (0) $

  These compact balls have arbitrarily large radii. Every closed ball centered
  at $0$ is therefore a closed subset of one of them, hence is compact.
  Translation gives the same conclusion for balls with arbitrary center.
  This argument also shows that the existence of any one compact closed ball
  implies compactness of every closed ball.
]

#corollary(title: "Local Fields Are Complete")[
  Every local field is complete.
]

#proof[
  Let $(x_n)$ be a Cauchy sequence. Its tail lies in a closed ball, which is
  compact by the compact-ball criterion. The tail therefore has a convergent
  subsequence $x_(n_j)->x$. For every $epsilon>0$, the Cauchy property gives
  $N$ such that

  $ m,n>=N => abs(x_m-x_n)<epsilon/2 $

  Taking $n=n_j>=N$ and then letting $j$ grow shows that
  $abs(x_m-x)<=epsilon/2<epsilon$ for every sufficiently large $m$. Thus the
  whole sequence converges to $x$.
]

#remark(title: "Completeness Is Not Enough")[
  Local compactness implies completeness, but the converse is false. For
  example, the completion of $QQ_p (t)$ for the Gauss norm has an infinite
  residue field and is not locally compact. The missing ingredient is
  #emph[finite branching at each level of precision].
]

=== First Examples and Nonexamples

#example(title: "Archimedean Fields")[
  With their usual absolute values, $RR$ and $CC$ are local fields: their
  closed bounded balls are compact. The field $QQ$ is not local because it is
  not complete; for instance, a rational Cauchy sequence converging to
  $sqrt(2)$ has no limit in $QQ$.
]

#example(title: "Finite Fields")[
  A finite field has no nontrivial absolute value. Indeed, every nonzero
  element has finite multiplicative order, so multiplicativity forces its
  absolute value to be $1$. Finite fields are therefore residue fields of
  local fields, but are not local fields under our convention.
]

#remark(title: "The Word Local")[
  A local field is not a local ring: it is a field, so its only maximal ideal
  is zero. The terminology comes from its origin. Completing a global field at
  one absolute value, or #emph[one place], discards all other places and
  retains one local arithmetic world.
]

=== The Nonarchimedean Criterion

Let $K$ now be a field with a nontrivial nonarchimedean absolute value. Recall
the associated valuation ring, maximal ideal, and residue field

$ cal(O)_K:={x in K:abs(x)<=1}, quad frak(m)_K:={x in K:abs(x)<1}, quad kappa_K:=cal(O)_K slash frak(m)_K $

The ring $cal(O)_K$ is the closed unit ball, while $frak(m)_K$ is the open unit
ball. Both are open and closed additive subgroups: this is one of the places
where ultrametric geometry and algebra become the same structure.

#theorem(title: "Equivalent Characterizations of a Nonarchimedean Local Field")[
  For a nontrivially valued nonarchimedean field $K$, the following conditions
  are equivalent.

  + The field $K$ is locally compact.

  + The ring of integers $cal(O)_K$ is compact.

  + The field $K$ is complete, its absolute value is induced by a discrete
    valuation, and its residue field $kappa_K$ is finite.
]

#proof[
  Suppose first that $K$ is locally compact. The compact-ball criterion makes
  the closed unit ball $cal(O)_K$ compact, and the preceding corollary makes
  $K$ complete.

  The cosets of $frak(m)_K$ in $cal(O)_K$ are open and form a disjoint open
  cover of $cal(O)_K$. Compactness gives a finite subcover, so
  $kappa_K=cal(O)_K slash frak(m)_K$ is finite.

  It remains to see that the valuation is discrete. If the additive value
  group were not discrete, the elementary structure theorem for subgroups of
  $RR$ would make it dense. We could then choose $x_n in frak(m)_K$ with

  $ abs(x_n)->1 $

  Compactness of $cal(O)_K$ would give a convergent subsequence with limit
  $x in cal(O)_K$, and continuity would give $abs(x)=1$. But
  $abs(x_n)<abs(x)$ forces

  $ abs(x_n-x)=abs(x)=1 $

  by the rigid-triangle property, contradicting convergence. Thus the value
  group is discrete and, after rescaling, is $ZZ$.

  The implication from compactness of $cal(O)_K$ to local compactness is
  immediate, because $cal(O)_K$ is a neighborhood of $0$ and its translates
  are neighborhoods of all points.

  Finally, suppose that $K$ is complete for a discrete valuation and that
  $kappa_K$ is finite. Choose a uniformizer $pi$. Completeness identifies

  $ cal(O)_K tilde.eq varprojlim(n) cal(O)_K slash pi^n cal(O)_K $

  Each quotient on the right is finite: its filtration has $n$ successive
  quotients isomorphic to the finite additive group $kappa_K$. A finite
  discrete space is compact, and an inverse limit of compact spaces is compact.
  Therefore $cal(O)_K$ is compact, completing the cycle of implications.
]

#quote[
  local compactness $approx$ completeness $+$ finitely many choices at every
  finite level of precision
]

The theorem gives the most useful intrinsic definition in arithmetic:

#definition(title: "Nonarchimedean Local Field, Arithmetic Form")[
  Equivalently, a #emph[nonarchimedean local field] is a complete discretely
  valued field with finite residue field.

  Choose the normalized valuation and write

  $ v_K:K^times->ZZ, quad frak(m)_K=(pi), quad q:=|kappa_K| $

  The #emph[normalized absolute value] is

  $ abs(x)_K:=q^(-v_K (x)), quad abs(0)_K:=0 $

  Thus $abs(pi)_K=q^(-1)$. Any other absolute value defining the same topology
  is a positive power of this one.
]

== Arithmetic Structure and Examples

The compact unit ball contains the entire finite-precision structure of a
nonarchimedean local field.

#proposition(title: "Balls, Units, and Precision")[
  Let $K$ be a nonarchimedean local field, with uniformizer $pi$ and residue
  field of cardinality $q$. Then:

  + for every $a in K$ and $n in ZZ$,

    $ B_(<=q^(-n)) (a)=a+pi^n cal(O)_K $

  + every ball is both open and closed, and every closed ball is compact;

  + for $n>=1$,

    $ |cal(O)_K slash frak(m)_K^n|=q^n $

  + there is an isomorphism of topological rings

    $ cal(O)_K tilde.eq varprojlim(n) cal(O)_K slash frak(m)_K^n $

  + every nonzero element has a unique expression $x=pi^n u$ with
    $n in ZZ$ and $u in cal(O)_K^times$, so

    $ K^times tilde.eq pi^ZZ times cal(O)_K^times $
]

#proof[
  The first formula is simply the equivalence

  $ abs(x-a)_K<=q^(-n) <=> v_K (x-a)>=n <=> x-a in pi^n cal(O)_K $

  It identifies balls with additive cosets of fractional ideals. Such cosets
  are open and closed in an ultrametric space, and compactness follows from the
  compact-ball criterion.

  Multiplication by $pi^i$ identifies each successive quotient
  $frak(m)_K^i slash frak(m)_K^(i+1)$ with $kappa_K$. The filtration from
  $cal(O)_K slash frak(m)_K^n$ therefore has $n$ layers, each of size $q$,
  proving the cardinality formula. Completeness and separatedness give the
  inverse-limit description. Finally, taking $n=v_K (x)$ makes
  $u=pi^(-n)x$ a unit, and the valuation proves uniqueness.
]

#remark(title: "Profinite Integers")[
  The inverse-limit description shows that $cal(O)_K$ is a #emph[profinite
  ring]: it is assembled from the finite rings
  $cal(O)_K slash frak(m)_K^n$. Topologically it is compact, Hausdorff, and
  totally disconnected. The field itself is the increasing union

  $ K=union_(n>=0) pi^(-n) cal(O)_K $

  of compact open balls, so it is locally compact but not compact.
]

#remark(title: "Formal-Geometric Picture")[
  The scheme $Spec cal(O)_K$ has a generic point with residue field $K$ and
  one closed point with residue field $kappa_K$. The quotients

  $ cal(O)_K slash frak(m)_K^n $

  are successive infinitesimal thickenings of that closed point. Hence
  $cal(O)_K tilde.eq varprojlim(n) cal(O)_K slash frak(m)_K^n$ says that the
  integer ring remembers the entire formal neighborhood of the closed point,
  while passing to $K$ removes the closed point by inverting $pi$.
]

#remark(title: "Open Balls versus Closed Balls")[
  In a discretely valued field, only the radii $q^n$ occur as nonzero
  distances. Consequently an open ball of a displayed real radius may already
  equal a closed ball of a smaller radius. In particular, the topological
  closure of $B_(<r) (a)$ need not be $B_(<=r) (a)$: the open ball is already
  closed.
]

=== Fundamental Examples

#example(title: [The Field $QQ_p$])[
  The field $QQ_p$ is complete for the $p$-adic valuation, its ring of integers
  is $ZZ_p$, its uniformizer is $p$, and its residue field is $FF_p$.
  Therefore

  $ cal(O)_(QQ_p)=ZZ_p, quad frak(m)_(QQ_p)=p ZZ_p, quad abs(x)_p=p^(-v_p (x)) $

  The compactness of $ZZ_p$ can be read directly from

  $ ZZ_p tilde.eq varprojlim(n) ZZ slash p^n ZZ $

  Each finite quotient records one level of precision.
]

#example(title: [Finite Extensions of $QQ_p$])[
  If $L slash QQ_p$ is finite, then the unique extension of the $p$-adic
  absolute value makes $L$ a local field. Its ring of integers $cal(O)_L$ is a
  complete DVR and its residue field is a finite extension $FF_(p^f)$ of
  $FF_p$. These are precisely the nonarchimedean local fields of
  characteristic zero.
]

#example(title: "Laurent-Series Fields")[
  Let $q$ be a prime power. For a nonzero Laurent series

  $ x=sum_(n=N)^infinity a_n t^n, quad a_N!=0 $

  put $v_t (x)=N$ and $abs(x)=q^(-N)$. Then

  $ cal(O)_(FF_q ((t)))=FF_q [[t]], quad frak(m)=(t), quad k=FF_q $

  The field $FF_q ((t))$ is complete, and the residue field is finite, so it is
  a local field. This is the equal-characteristic analogue of $QQ_p$.
]

#example(title: "Why the Coefficient Field Must Be Finite")[
  For an arbitrary field $k$, the field $k((t))$ is complete and discretely
  valued, but it is locally compact if and only if $k$ is finite. Indeed, the
  cosets of $t k[[t]]$ give an open cover of the unit ball indexed by the
  residue field $k$. If $k$ is infinite, no finite subcover exists.
]

== Global Completions and Classification

=== Completions of Global Fields

The definition of a local field is intrinsic, but its main examples arise by
completing global fields. Recall that a #emph[global field] is either a number
field, a finite extension of $QQ$, or a global function field, a finite
extension of $FF_q (t)$.

#corollary(title: "Global Completions Are Local")[
  Let $F$ be a global field and let $abs(dot)_v$ be a nontrivial absolute value
  on $F$. Then its completion $F_v$ is a local field.
]

#proofsketch[
  At an archimedean place of a number field, the completion is $RR$ or $CC$.
  At a nonarchimedean place, the corresponding prime ideal gives a discrete
  valuation. The completed field is complete by construction, and its residue
  field is finite because it is a finite extension of a finite prime field.
  The nonarchimedean criterion therefore applies.
]

#remark(title: "A Place as a Direction of Magnification")[
  Passing from $F$ to $F_v$ chooses one notion of smallness and permits limits
  only in that direction. For a number field, an archimedean place magnifies
  its real or complex geometry, while a prime ideal magnifies congruences
  modulo higher and higher powers of that prime.
]

=== Classification of Local Fields

We use one standard topological fact, analogous to the finite-dimensionality
of a locally compact normed vector space.

#proposition(title: "Locally Compact Vector Spaces")[
  A locally compact topological vector space over a nondiscrete locally
  compact field is finite-dimensional.
]

#proofsketch[
  If the space were infinite-dimensional, one could inductively choose
  vectors whose pairwise differences avoid a fixed smaller neighborhood of
  zero. After rescaling, all these vectors can be placed in one compact
  neighborhood. This produces an infinite uniformly separated subset of a
  compact space, contradicting total boundedness. This is the topological
  vector-space version of the usual Riesz-lemma argument.
]

#theorem(title: "Classification of Local Fields")[
  Let $K$ be a local field.

  + If its absolute value is archimedean, then $K$ is topologically isomorphic
    to $RR$ or $CC$.

  + If it is nonarchimedean of characteristic zero, then $K$ is a finite
    extension of $QQ_p$ for a unique prime $p$.

  + If it has positive characteristic $p$, then $K$ is a finite extension of
    $FF_q ((t))$ for some power $q$ of $p$.
]

#proof[
  Every local field is complete. In the archimedean case, the restriction to
  the prime field $QQ$ is equivalent to the usual absolute value by
  Ostrowski's theorem. Completeness embeds $RR$ as a closed subfield of $K$.
  The preceding vector-space proposition makes $K$ finite-dimensional over
  $RR$, and the classification of finite field extensions of $RR$ gives
  $K tilde.eq RR$ or $K tilde.eq CC$.

  Now suppose that $K$ is nonarchimedean of characteristic zero. Its finite
  residue field has characteristic $p$ for a unique prime $p$, and
  $p in frak(m)_K$. The restriction of the absolute value to $QQ$ is therefore
  equivalent to the $p$-adic absolute value. Completeness embeds $QQ_p$ as a
  closed subfield of $K$. Both fields are locally compact and nondiscrete, so
  the vector-space proposition gives $[K:QQ_p]<infinity$.

  Finally, suppose $"char"(K)=p>0$. Choose $s in K$ with $abs(s)!=1$. Such an
  $s$ cannot be algebraic over the finite prime field, so it is transcendental
  over $FF_p$. The closure in $K$ of $FF_p (s)$ is one of
  its nonarchimedean completions, hence is topologically isomorphic to
  $FF_q ((t))$ for some finite extension $FF_q slash FF_p$. Applying the same
  vector-space proposition once more shows that $K$ is finite over this
  subfield.
]

#quote[
  There are only three local worlds: the real-complex world, mixed
  characteristic $p$-adic worlds, and equal-characteristic Laurent-series
  worlds.
]

The next layer of local theory asks when an approximate solution to a
polynomial equation lifts to an exact solution. That is the role of Hensel's
lemma, whose effectiveness rests precisely on the completeness developed
above.

== Hensel's Lemma and Its Variants

Throughout this section, $K$ is a nonarchimedean local field with ring of
integers $cal(O)=cal(O)_K$, maximal ideal $frak(m)=(pi)$, normalized valuation
$v=v_K$, and residue field $kappa=cal(O) slash frak(m)$. For
$f in cal(O)[X]$, write $overline(f) in kappa[X]$ for its reduction modulo
$frak(m)$.

#quote[
  Hensel's lemma turns a sufficiently nondegenerate approximate root into a
  unique exact root by repeatedly correcting one error with the derivative.
]

=== The Formal Taylor Estimate

Recall that if

$ f(X)=sum_(i=0)^d c_i X^i $

then its formal derivative is

$ f'(X)=sum_(i=1)^d i c_i X^(i-1) $

This definition works over rings of arbitrary characteristic; it does not
require division by factorials.

#lemma(title: "First-Order Taylor Formula")[
  Let $R$ be a commutative ring, let $f in R[X]$, and let $a in R$. There is a
  unique polynomial $g in R[X]$ such that

  $ f(X)=f(a)+f'(a)(X-a)+(X-a)^2 g(X) $
]

#proof[
  Expand each monomial $X^i=(a+(X-a))^i$ by the binomial theorem. The terms of
  degrees zero and one in $X-a$ are $a^i$ and $i a^(i-1)(X-a)$; all remaining
  terms are divisible by $(X-a)^2$. Summing with coefficients $c_i$ gives the
  formula. Uniqueness follows because the monic polynomial $(X-a)^2$ is not a
  zero divisor in $R[X]$.
]

#corollary(title: "Taylor Estimates in the Unit Ball")[
  If $f in cal(O)[X]$ and $a,b in cal(O)$, then

  $ abs(f(b)-f(a)-f'(a)(b-a))<=abs(b-a)^2 $

  and

  $ abs(f'(b)-f'(a))<=abs(b-a) $
]

#proof[
  Apply the Taylor formula to $f$ and then to $f'$. Every polynomial in
  $cal(O)[X]$ has absolute value at most $1$ at every point of $cal(O)$, so the
  remaining factors contribute no larger absolute value.
]

#remark(title: "Linearization")[
  The equation

  $ f(a+h)=f(a)+f'(a)h+O(h^2) $

  should be read literally in the valuation topology: the discarded error has
  at least twice the valuation of $h$. If $f'(a)$ is a unit, the linear
  equation $f(a)+f'(a)h=0$ determines a correction, while the new error is
  quadratic.
]

=== Simple Roots Lift

#definition(title: "Simple Residue Root")[
  An element $overline(a) in kappa$ is a #emph[simple root] of
  $overline(f)$ if

  $ overline(f)(overline(a))=0, quad overline(f)'(overline(a))!=0 $

  Equivalently, any lift $a_0 in cal(O)$ satisfies

  $ f(a_0) in frak(m), quad f'(a_0) in cal(O)^times $
]

#theorem(title: "Hensel's Lemma, Simple-Root Form")[
  Let $f in cal(O)[X]$ and suppose that $overline(a) in kappa$ is a simple
  root of $overline(f)$. Then there is a unique $a in cal(O)$ such that

  $ f(a)=0, quad a mod frak(m)=overline(a) $

  The polynomial $f$ need not be monic.
]

#proof[
  Choose a lift $a_0 in cal(O)$ of $overline(a)$ and define the Newton
  sequence

  $ a_(n+1):=a_n-f(a_n)/(f'(a_n)) $

  We prove inductively that

  $ a_n equiv a_0 mod frak(m), quad f'(a_n) in cal(O)^times, quad f(a_n) in frak(m)^(2^n) $

  These statements hold at $n=0$. If they hold at $n$, then
  $delta_n:=f(a_n)/(f'(a_n))$ belongs to $frak(m)^(2^n)$, so
  $a_(n+1)=a_n-delta_n$ remains congruent to $a_0$ modulo $frak(m)$. Hence
  $f'(a_(n+1))$ has the same nonzero residue as $f'(a_0)$ and is still a unit.
  The Taylor formula gives

  $ f(a_(n+1))=f(a_n)-f'(a_n)delta_n+delta_n^2 g_n=delta_n^2 g_n $

  for some $g_n in cal(O)$. Thus

  $ f(a_(n+1)) in frak(m)^(2^(n+1)) $

  which completes the induction.

  Since

  $ a_(n+1)-a_n in frak(m)^(2^n) $

  the sequence is Cauchy. Completeness of $cal(O)$ gives a limit
  $a in cal(O)$, and continuity gives $f(a)=0$ and
  $a equiv a_0 mod frak(m)$.

  For uniqueness, suppose $b$ is another root with
  $b equiv a mod frak(m)$. Taylor expansion at $a$ gives

  $ 0=f(b)-f(a)=(b-a)(f'(a)+(b-a)g(b)) $

  The second factor is a unit because $f'(a)$ is a unit and
  $b-a in frak(m)$. Since $cal(O)$ is a domain, $b=a$.
]

#remark(title: "One Root at Every Precision")[
  The lifted root determines a compatible tower

  $ a mod frak(m), quad a mod frak(m)^2, quad a mod frak(m)^3, quad dots $

  Conversely, Hensel lifting constructs this tower step by step and
  completeness turns it into one element of $cal(O)$. The simple-root
  condition is what makes the lift unique at every stage.
]

=== The Newton--Hensel Form

The simple-root hypothesis forces $f'(a_0)$ to be a unit. A more flexible
version allows the derivative to have positive valuation, provided the value
of $f(a_0)$ is even smaller.

#theorem(title: "Hensel's Lemma, Newton Form")[
  Let $f in cal(O)[X]$ and $a_0 in cal(O)$. Suppose

  $ abs(f(a_0))<abs(f'(a_0))^2 $

  or equivalently

  $ v(f(a_0))>2v(f'(a_0)) $

  Put

  $ lambda:=abs(f'(a_0)), quad epsilon:=abs(f(a_0))/lambda^2<1 $

  Then the Newton sequence

  $ a_(n+1):=a_n-f(a_n)/(f'(a_n)) $

  is well-defined in $cal(O)$ and converges to a root $a$ of $f$. More
  precisely,

  $ abs(f(a_n))<=epsilon^(2^n) lambda^2 $

  and

  $ abs(a_(n+1)-a_n)<=epsilon^(2^n) lambda $

  The limit is the unique root in the ball

  $ B_(<lambda) (a_0) $

  If $f(a_0)!=0$, then

  $ abs(a-a_0)=abs(f(a_0)/(f'(a_0))) $
]

#proof[
  Put $delta_n=f(a_n)/(f'(a_n))$. We prove simultaneously that

  $ abs(f'(a_n))=lambda, quad abs(f(a_n))<=epsilon^(2^n) lambda^2 $

  The assertions hold at $n=0$. They imply

  $ abs(delta_n)<=epsilon^(2^n) lambda<lambda<=1 $

  so $a_(n+1)=a_n-delta_n$ remains in $cal(O)$. The derivative estimate gives

  $ abs(f'(a_(n+1))-f'(a_n))<=abs(delta_n)<lambda $

  and the rigid-triangle property therefore yields
  $abs(f'(a_(n+1)))=lambda$. Taylor expansion at $a_n$ cancels the linear
  term and gives

  $ abs(f(a_(n+1)))<=abs(delta_n)^2<=epsilon^(2^(n+1)) lambda^2 $

  This proves the induction and the two displayed estimates.

  Since $epsilon^(2^n)lambda$ tends to zero, $(a_n)$ is Cauchy. Its limit
  $a in cal(O)$ satisfies $f(a)=0$. The first displacement has absolute value
  $epsilon lambda$, while every later displacement is strictly smaller; the
  ultrametric inequality gives the asserted value of $abs(a-a_0)$.

  Suppose $b$ is a root with $abs(b-a_0)<lambda$. The constructed root also
  lies in this ball, so $abs(a-b)<lambda$. Taylor expansion gives

  $ 0=f(b)-f(a)=(b-a)(f'(a)+(b-a)g(b)) $

  Here $abs(f'(a))=lambda$, while the second summand in the parentheses has
  absolute value strictly less than $lambda$. The parenthetical factor is
  therefore nonzero, forcing $b=a$.
]

#corollary(title: "Valuation and Congruence Forms")[
  Let $s=v(f'(a_0))$. If

  $ f(a_0) equiv 0 mod pi^(2s+1) $

  then $f$ has a unique root $a$ satisfying

  $ a equiv a_0 mod pi^(s+1) $

  More generally, if $v(f(a_0))=r>2s$, then

  $ v(a-a_0)=r-s $
]

#proof[
  The congruence gives $v(f(a_0))>=2s+1>2s$, so the Newton form applies. Its
  distance formula becomes

  $ v(a-a_0)=v(f(a_0))-v(f'(a_0))=r-s $
]

#remark(title: "Quadratic Convergence")[
  The exponent $2^n$ means that each Newton step approximately doubles the
  known precision. Over $RR$, Newton's method may leave the region of
  convergence; over a nonarchimedean field, the strict inequality
  $abs(f(a_0))<abs(f'(a_0))^2$ traps every iterate in one ball and guarantees
  convergence.
]

=== Lifting Coprime Factorizations

Hensel's lemma can lift more than a single root. A simple residue root is the
linear factor $X-overline(a)$; the following version lifts any decomposition
whose factors do not meet in the special fiber.

#theorem(title: "Hensel's Lemma, Factorization Form")[
  Let $f in cal(O)[X]$ be monic and suppose

  $ overline(f)=g_0 h_0 $

  for coprime monic polynomials $g_0,h_0 in kappa[X]$. Then there are unique
  monic polynomials $g,h in cal(O)[X]$ such that

  $ f=g h, quad overline(g)=g_0, quad overline(h)=h_0 $

  with $deg(g)=deg(g_0)$ and $deg(h)=deg(h_0)$.
]

#proof[
  Put $r=deg(g_0)$ and $s=deg(h_0)$. Choose monic lifts $g_1,h_1$ of degrees
  $r,s$. We inductively construct monic polynomials $g_n,h_n$ with these fixed
  degrees and

  $ f equiv g_n h_n mod pi^n $

  Suppose $g_n,h_n$ have been constructed and write

  $ E_n:=(f-g_n h_n)/pi^n in cal(O)[X] $

  Since both $f$ and $g_n h_n$ are monic of degree $r+s$, one has
  $deg(E_n)<r+s$. Coprimality of $g_0$ and $h_0$ makes the linear map

  $ {u in kappa[X]:deg(u)<r} times {w in kappa[X]:deg(w)<s}
    -> {E in kappa[X]:deg(E)<r+s} $

  $ (u,w) mapsto u h_0+w g_0 $

  an isomorphism. Indeed, injectivity follows from Euclid's lemma and the
  degree bounds, and both sides have dimension $r+s$ over $kappa$.

  We may therefore choose lifts $u_n,w_n in cal(O)[X]$ of the unique pair
  satisfying

  $ overline(E_n)=overline(u_n)h_0+overline(w_n)g_0 $

  with $deg(u_n)<r$ and $deg(w_n)<s$. Set

  $ g_(n+1)=g_n+pi^n u_n, quad h_(n+1)=h_n+pi^n w_n $

  Expanding the product shows

  $ f-g_(n+1)h_(n+1) in pi^(n+1) cal(O)[X] $

  Thus the induction continues. Each coefficient sequence is Cauchy, so
  completeness produces monic limits $g,h$ with $f=g h$ and the required
  reductions. The same correction argument applied at the first level at
  which two lifts differ proves uniqueness.
]

#corollary(title: "Simple Roots from Factorization")[
  If $overline(a)$ is a simple root of $overline(f)$ and $f$ is monic, then

  $ overline(f)=(X-overline(a))h_0 $

  with $X-overline(a)$ coprime to $h_0$. The factorization form lifts this to

  $ f=(X-a)h $

  and therefore recovers the simple-root form.
]

#theorem(title: "Hensel's Lemma, General Factorization Form")[
  Let $f in cal(O)[X]$ be arbitrary and suppose

  $ overline(f)=g_0 h_0 $

  for coprime polynomials $g_0,h_0 in kappa[X]$, with $g_0$ monic. Then there
  are polynomials $g,h in cal(O)[X]$ such that

  $ f=g h, quad overline(g)=g_0, quad overline(h)=h_0, quad deg(g)=deg(g_0) $
]

#proof[
  Put $r=deg(g_0)$ and $d=deg(f)$. Choose a monic lift $g_1$ of $g_0$ of
  degree $r$, and divide $f$ by $g_1$. The quotient gives $h_1$, and the
  remainder lies in $pi cal(O)[X]$, so

  $ f equiv g_1 h_1 mod pi $

  Suppose $f equiv g_n h_n mod pi^n$, where $g_n$ is monic of degree $r$ and
  $deg(h_n)<=d-r$. Put $E_n=(f-g_n h_n)/pi^n$. Euclidean division modulo
  $pi$ and the coprimality of $g_0,h_0$ give polynomials
  $u_n,w_n in cal(O)[X]$ satisfying

  $ overline(E_n)=overline(u_n)h_0+overline(w_n)g_0 $

  with $deg(u_n)<r$ and $deg(w_n)<=d-r$. Indeed, multiplication by $h_0$ is
  invertible in $kappa[X] slash (g_0)$, which first determines $u_n$; the
  quotient then determines $w_n$.

  The corrections

  $ g_(n+1)=g_n+pi^n u_n, quad h_(n+1)=h_n+pi^n w_n $

  improve the congruence to modulus $pi^(n+1)$ without changing the degree or
  leading coefficient of $g_n$. Completeness produces polynomial limits
  $g,h$ with the required properties.
]

== Henselian Rings and Henselization

Hensel's lemma is not merely a theorem about complete valued fields. It
isolates a property of a local ring itself: every solution that is
nondegenerate on the closed fiber already comes from a solution over the
whole local ring. This is the algebraic content of being #emph[henselian].

=== Definition and Equivalent Characterizations

#definition(title: "Henselian Local Ring")[
  Let $(A,frak(m),kappa)$ be a local ring, where
  $kappa=A slash frak(m)$. We call $A$ #emph[henselian] if, for every monic
  $f in A[X]$ and every $overline(a) in kappa$ satisfying

  $ overline(f)(overline(a))=0, quad overline(f)'(overline(a))!=0 $

  there is a unique $a in A$ such that

  $ a mod frak(m)=overline(a), quad f(a)=0 $
]

For any ring $R$, write

$ "Idem"(R):={e in R | e^2=e} $

for the set of its idempotents.

#theorem(title: "Equivalent Henselian Properties")[
  For a local ring $(A,frak(m),kappa)$, the following conditions are
  equivalent.

  + The ring $A$ is henselian.

  + Every simple root of a monic polynomial over $kappa$ lifts uniquely to a
    root over $A$.

  + If $f in A[X]$ is monic and

    $ overline(f)=g_0 h_0 $

    is a factorization into coprime monic polynomials in $kappa[X]$, then
    there is a unique factorization $f=g h$ into monic polynomials whose
    reductions are $g_0,h_0$.

  + For every finite $A$-algebra $B$, reduction induces a bijection

    $ "Idem"(B) tilde.eq "Idem"(B slash frak(m)B) $

  + Every finite $A$-algebra is a finite product of local rings.

  + Let $A->B$ be étale and let $frak(q) in Spec B$ lie over $frak(m)$. If
    the residue-field map $kappa->kappa(frak(q))$ is an isomorphism, then the
    pointed étale neighborhood $(B,frak(q))$ admits a unique local
    $A$-algebra retraction $B_(frak(q))->A$.
]

#proofsketch[
  A lifted factorization with one factor $X-a$ gives the simple-root
  property. Conversely, if $g_0$ and $h_0$ are coprime, a Bézout identity
  lets one correct arbitrary lifts one order at a time; equivalently, the
  factors determine the idempotents $(1,0)$ and $(0,1)$ in the corresponding
  product algebra. Thus factorization lifting is the same as idempotent
  lifting. Iterating the lifted primitive idempotents decomposes every finite
  algebra into local factors.

  Finally, near a point at which an étale algebra has the standard form
  $A[X] slash (f)$, the residue point is a simple root of $overline(f)$.
  Lifting that root is precisely an $A$-section through the chosen point.
  This identifies the polynomial and pointed-étale formulations.
]

#remark(title: "Geometric Reading")[
  The condition $overline(f)'(overline(a))!=0$ says that the point
  $overline(a)$ on the closed fiber of

  $ Spec (A[X] slash (f))->Spec A $

  is étale. Henselianity says that this isolated unramified point extends
  uniquely to an $A$-point. The idempotent formulation says the same thing
  globally: every decomposition into open-and-closed pieces visible on the
  closed fiber already comes from a decomposition upstairs.
]

=== Henselianity versus Completeness

#theorem(title: "Complete Local Rings Are Henselian")[
  If the local ring $(A,frak(m))$ is separated and complete for its
  $frak(m)$-adic topology, then $A$ is henselian.
]

#proof[
  Let $f in A[X]$ be monic and let $a_1 in A$ lift a simple root modulo
  $frak(m)$. Suppose inductively that

  $ f(a_n) in frak(m)^n $

  Since $f'(a_n)$ is a unit, multiplication by $f'(a_n)$ is invertible on
  $frak(m)^n slash frak(m)^(n+1)$. We may therefore choose
  $u_n in frak(m)^n$ such that

  $ f(a_n)+f'(a_n)u_n equiv 0 mod frak(m)^(n+1) $

  and put $a_(n+1)=a_n+u_n$. Taylor expansion gives

  $ f(a_(n+1)) equiv 0 mod frak(m)^(n+1) $

  while $a_(n+1) equiv a_n mod frak(m)^n$. Thus $(a_n)$ is an
  $frak(m)$-adic Cauchy sequence. Completeness gives $a=lim a_n in A$;
  continuity of polynomial evaluation gives $f(a)=0$. If $a,b$ are two
  lifts, then

  $ 0=f(a)-f(b)=(a-b)g(a,b) $

  where $g(a,b) equiv f'(overline(a)) mod frak(m)$ is a unit, so $a=b$.
]

#example(title: "Basic Complete Examples")[
  The rings $ZZ_p$ and $k[[t]]$ are complete for their maximal-ideal
  topologies; hence both are henselian. More generally, every complete DVR
  and every complete noetherian local ring is henselian.
]

#remark(title: "The Converse Fails")[
  Henselian does not imply complete. For example, the henselization
  $ZZ_((p))^h$ is henselian by construction, but its completion is $ZZ_p$ and
  it is strictly smaller than $ZZ_p$. One quick way to see strictness is that
  $ZZ_((p))^h$ is a filtered colimit over a countable collection of finite
  type étale neighborhoods and is therefore countable, whereas $ZZ_p$ is
  uncountable.

  #quote[
    Completeness supplies limits for all compatible $frak(m)$-adic
    approximations; henselianity only guarantees the lifting of étale, or
    equivalently nondegenerate algebraic, approximations.
  ]
]

=== The Closed Fiber Controls Finite Étale Geometry

The strongest geometric consequence of henselianity is that finite étale
geometry cannot distinguish the local scheme from its closed point.

#theorem(title: "Finite Étale Algebras over a Henselian Local Ring")[
  Let $(A,frak(m),kappa)$ be henselian. Reduction to the closed fiber is an
  equivalence of categories

  $ "FinEt"(A) tilde.eq "FinEt"(kappa), quad B mapsto B slash frak(m)B $

  Equivalently, pullback along $Spec kappa->Spec A$ induces

  $ {"finite étale covers of " Spec A} tilde.eq {"finite étale covers of " Spec kappa} $
]

#proofsketch[
  Let $B$ be a finite étale $A$-algebra. The special fiber
  $B slash frak(m)B$ is a finite product of finite separable field extensions
  of $kappa$. Henselian idempotent lifting raises the primitive idempotents of
  this product uniquely to $B$, so $B$ decomposes into the corresponding
  local factors.

  Conversely, write a finite separable extension of $kappa$ as
  $kappa[X] slash (overline(f))$ with $overline(f)$ separable, and lift
  $overline(f)$ to a monic polynomial $f in A[X]$. The discriminant of $f$
  reduces to the nonzero discriminant of $overline(f)$, hence is a unit in
  $A$. Therefore $A[X] slash (f)$ is already finite étale over $A$. Products
  give the general case. Finally, morphisms between finite étale algebras are
  themselves parametrized by a finite étale $A$-scheme. The simple-root
  property gives a unique $A$-point above each of its $kappa$-points, proving
  full faithfulness.
]

#corollary(title: "Étale Fundamental Group")[
  Choose a geometric closed point
  $overline(s):Spec kappa^"sep"->Spec A$. Then

  $ pi_1^"étale" (Spec A,overline(s)) tilde.eq "Gal"(kappa^"sep" slash kappa) $

  In particular, if $kappa$ is separably closed, every finite étale
  $A$-algebra is a finite product of copies of $A$, and the étale fundamental
  group is trivial. A henselian local ring with separably closed residue
  field is called #emph[strictly henselian].
]

#proof[
  The preceding equivalence preserves finite limits, disjoint unions, and
  the fiber functor at $overline(s)$. It is therefore an equivalence of the
  associated Galois categories. Taking automorphism groups of their common
  fiber functor yields the displayed isomorphism.
]

#quote[
  From the finite étale point of view, a henselian local scheme is its closed
  point.
]

This slogan concerns finite étale covers only; it does not say that
$Spec A$ and $Spec kappa$ are isomorphic as schemes. Nilpotent, formal, and
positive-dimensional information is still present in $Spec A$.

=== Henselization: the Étale-Local Neighborhood

#definition(title: "Henselization")[
  Let $(A,frak(m),kappa)$ be a local ring. Its #emph[henselization] is a local
  map

  $ A->A^h $

  such that $A^h$ is henselian and the following universal property holds:
  every local map $A->R$ to a henselian local ring factors uniquely through
  $A^h$. The residue field is unchanged,

  $ A^h slash frak(m)A^h tilde.eq kappa $
]

#theorem(title: "Construction by Pointed Étale Neighborhoods")[
  A #emph[pointed étale neighborhood] of $(A,frak(m))$ is a pair
  $(B,frak(q))$ such that $A->B$ is étale, $frak(q)$ lies over $frak(m)$,
  and $kappa->kappa(frak(q))$ is an isomorphism. These neighborhoods form a
  filtered system, and

  $ A^h tilde.eq varinjlim((B,frak(q)) in "EtNbh"(A,frak(m))) B_(frak(q)) $

  The map $A->A^h$ is flat and local, its maximal ideal is
  $frak(m)A^h$, and it induces the identity on the residue field.
]

#proofsketch[
  Étale morphisms are stable under composition and fiber product, which makes
  pointed étale neighborhoods filtered. Their local rings all have residue
  field $kappa$, so the filtered colimit is local with the same residue
  field. Given a monic polynomial and a simple root on the closed fiber,
  adjoin a root and localize at the point selected by that residue root. This
  is a standard pointed étale neighborhood, so its root appears at a later
  stage of the filtered system. Hence the colimit is henselian. The same
  finite-presentation argument proves the universal property. Flatness
  follows because étale maps and localization are flat, and filtered colimits
  preserve flatness.
]

#remark(title: "Geometric Meaning")[
  Contravariantly, $Spec A^h->Spec A$ is assembled from all étale
  neighborhoods equipped with the chosen point above the closed point. Thus
  $Spec A^h$ is the #emph[étale-local neighborhood] of that point: it keeps
  algebraic information detectable without ramification, but forgets the
  rest of the ambient scheme. The colimit on rings becomes a cofiltered limit
  of pointed étale neighborhoods on schemes.
]

#theorem(title: "Henselization and Completion")[
  Let $(A,frak(m))$ be a noetherian local ring. Then $A^h$ is noetherian and
  completion induces an isomorphism

  $ hat(A^h) tilde.eq hat(A) $

  Moreover, $A^h->hat(A)$ is faithfully flat.
]

#proofsketch[
  Pointed étale neighborhoods have the same completed local ring as $A$:
  étaleness makes each infinitesimal lifting unique, so their quotients modulo
  $frak(m)^n$ agree. Passing to the filtered colimit and then to the inverse
  limit gives

  $ varprojlim(n) A^h slash frak(m)^n A^h tilde.eq varprojlim(n) A slash frak(m)^n $

  which is the stated isomorphism. Noetherianity and faithful flatness are the
  standard finiteness consequences of the noetherian henselization theorem.
]

#remark(title: "Two Kinds of Locality")[
  Completion and henselization therefore have the same formal infinitesimal
  neighborhoods in the noetherian case, but they need not be the same ring.

  + $A^h$ is an étale and algebraic localization: it adjoins precisely the
    local algebraic solutions forced by Hensel's lemma.

  + $hat(A)$ is a formal and topological localization: it adjoins limits of
    arbitrary compatible $frak(m)$-adic approximations.

  For a DVR $A$ with fraction field $K$, after choosing compatible embeddings
  one may make the comparison concrete as

  $ A^h=hat(A) inter K^"sep" $

  inside an algebraic closure of the completed fraction field.
]

== Applications, Examples, and Exercises

The point of Hensel's lemma is practical: equations over a finite residue
field can be searched by brute force, while the lemma promotes each
nondegenerate solution to an exact solution in an infinite local field.

=== Digit-by-Digit Root Lifting

Newton iteration doubles precision, but for hand computation it is often
easier to lift one power of the uniformizer at a time.

#proposition(title: "One-Digit Hensel Step")[
  Let $f in cal(O)[X]$ and suppose $a_N in cal(O)$ satisfies

  $ f(a_N) equiv 0 mod pi^N, quad f'(a_N) in cal(O)^times $

  for some $N>=1$. There is a unique residue class
  $overline(t) in kappa$ such that, for any lift $t in cal(O)$,

  $ a_(N+1):=a_N+pi^N t $

  satisfies $f(a_(N+1)) equiv 0 mod pi^(N+1)$. It is determined by the linear
  equation

  $ overline(f(a_N)/pi^N)+overline(f'(a_N)) overline(t)=0 " in " kappa $
]

#proof[
  Taylor expansion gives

  $ f(a_N+pi^N t) equiv f(a_N)+pi^N t f'(a_N) mod pi^(N+1) $

  after dividing by $pi^N$ and reducing modulo $pi$. Since
  $overline(f'(a_N))!=0$, the displayed linear equation has exactly one
  solution in $kappa$.
]

#example(title: [Computing $sqrt(6)$ in $ZZ_5$])[
  Put $f(X)=X^2-6$. Modulo $5$,

  $ overline(f)(X)=X^2-1=(X-1)(X+1) $

  and both roots are simple. Starting with $a_1=1$, write
  $a_(N+1)=a_N+5^N t$. The one-digit equation successively gives

  $ a_1=1 mod 5 $

  $ a_2=16 mod 25 $

  $ a_3=16 mod 125 $

  $ a_4=516 mod 625 $

  These residues are compatible and converge to the unique
  $a in ZZ_5$ satisfying

  $ a^2=6, quad a equiv 1 mod 5 $

  Starting from $-1$ produces the other root $-a$.
]

#example(title: [A Multiple Residue Root: $sqrt(17)$ in $ZZ_2$])[
  For $f(X)=X^2-17$, reduction modulo $2$ gives
  $(X-1)^2$, so the simple-root form does not apply. At $a_0=1$, however,

  $ v_2 (f(1))=4>2=2v_2 (f'(1)) $

  The Newton--Hensel form applies. Its first approximations are

  $ a_0=1, quad a_1=9, quad a_2=49/9 $

  with

  $ v_2 (f(a_0))=4, quad v_2 (f(a_1))=6, quad v_2 (f(a_2))=10 $

  They converge to the unique square root $a$ of $17$ satisfying
  $a equiv 1 mod 8$; the other root satisfies $-a equiv 7 mod 8$.
]

=== Detecting Squares in Local Fields

Hensel's lemma reduces square classes to a valuation condition and a finite
residue-field calculation.

#theorem(title: [Squares in $QQ_p$])[
  Let $x in QQ_p^times$.

  + If $p$ is odd, write $x=p^n u$ with $u in ZZ_p^times$. Then $x$ is a
    square in $QQ_p$ if and only if $n$ is even and
    $overline(u) in FF_p^times$ is a square.

  + For $p=2$, write $x=2^n u$ with $u in ZZ_2^times$. Then $x$ is a square
    in $QQ_2$ if and only if

    $ n equiv 0 mod 2, quad u equiv 1 mod 8 $
]

#proof[
  A square necessarily has even valuation. Suppose first that $p$ is odd and
  $n=2m$. If $overline(u)=overline(a)^2$ in $FF_p^times$, then
  $f(X)=X^2-u$ has the simple residue root $overline(a)$, because
  $f'(a)=2a$ is a unit. Hensel's lemma gives $b in ZZ_p^times$ with $b^2=u$,
  and then $x=(p^m b)^2$. The converse follows by reduction modulo $p$.

  Now let $p=2$. The square of every odd integer is congruent to $1$ modulo
  $8$, proving necessity. Conversely, if $u equiv 1 mod 8$, then for
  $f(X)=X^2-u$ and $a_0=1$,

  $ v_2 (f(1))>=3>2=2v_2 (f'(1)) $

  so the Newton--Hensel form gives a square root of $u$ in $ZZ_2$. Multiplying
  by $2^(n/2)$ proves sufficiency.
]

#example(title: "Rapid Solvability Tests")[
  The criterion immediately gives:

  + $10$ is a square in $QQ_3$, since $v_3 (10)=0$ and
    $10 equiv 1 mod 3$;

  + $10$ is not a square in $QQ_5$, since $v_5 (10)=1$;

  + $17$ is a square in $QQ_2$, since $17 equiv 1 mod 8$;

  + $-1$ is a square in $QQ_p$ for odd $p$ exactly when
    $p equiv 1 mod 4$.
]

=== Teichmüller Representatives and Local Digits

Let $q=|kappa|$. The finite group $kappa^times$ has order $q-1$, which is
prime to the residue characteristic.

#theorem(title: "Teichmüller Lifts")[
  For every $overline(a) in kappa$, there is a unique element
  $[overline(a)] in cal(O)$ satisfying

  $ [overline(a)] mod frak(m)=overline(a), quad [overline(a)]^q=[overline(a)] $

  The map $overline(a) mapsto [overline(a)]$ is multiplicative. For
  $overline(a)!=0$, its image is the unique $(q-1)$st root of unity reducing
  to $overline(a)$.
]

#proof[
  Apply the simple-root form to

  $ f(X)=X^q-X $

  Every element of $kappa$ is a root of $overline(f)$, and

  $ overline(f)'(X)=q X^(q-1)-1=-1 $

  so every root is simple. This gives existence and uniqueness. The product
  $[overline(a)][overline(b)]$ is again fixed by the $q$th-power map and
  reduces to $overline(a)overline(b)$; uniqueness makes the lift
  multiplicative.
]

#corollary(title: "Canonical Digit Expansions")[
  Every $x in cal(O)$ has a unique convergent expansion

  $ x=sum_(n=0)^infinity [overline(a)_n] pi^n, quad overline(a)_n in kappa $

  Consequently every nonzero $x in K$ has a Laurent expansion of the same
  form with finitely many negative powers of $pi$.
]

#proof[
  Let $overline(a)_0$ be the residue of $x$. Then
  $x-[overline(a)_0] in pi cal(O)$, so divide by $pi$ and repeat. After $N$
  steps the error lies in $pi^N cal(O)$ and therefore tends to zero.
  Uniqueness follows by reducing successively modulo
  $pi,pi^2,pi^3,dots$.
]

#remark(title: [Connection with $p$-adic Digits])[
  For $K=QQ_p$, the Teichmüller digits form the multiplicative set

  $ {0} union mu_(p-1) subset.eq ZZ_p $

  rather than the ordinary representatives $0,1,dots,p-1$. In equal
  characteristic, they are exactly the constant coefficients in
  $FF_q [[t]]$. In mixed characteristic, they are the first hint of the Witt
  vector description of the maximal unramified subring of $cal(O)_K$.
]

=== Polynomial Factorization and Prime Splitting

#example(title: [Lifting $X^2+1$ over $ZZ_5$])[
  Modulo $5$ one has

  $ X^2+1=(X-2)(X+2) $

  with coprime factors. Hensel's lemma lifts them to two linear factors over
  $ZZ_5$. Thus there is a unique $i in ZZ_5$ with

  $ i^2=-1, quad i equiv 2 mod 5 $

  One further lift gives $i equiv 7 mod 25$. In particular,

  $ QQ_5 (i)=QQ_5 $
]

#proposition(title: [Local Splitting in $QQ(i)$])[
  Let $p$ be an odd prime. Then

  $ QQ(i) ⊗_QQ QQ_p tilde.eq cases(
    QQ_p times QQ_p quad & p equiv 1 mod 4,
    QQ_p (i) quad & p equiv 3 mod 4
  ) $

  In the first case the two roots of $X^2+1$ modulo $p$ lift to $QQ_p$; in
  the second case $QQ_p (i) slash QQ_p$ is the unramified quadratic extension.
  At $p=2$, the extension $QQ_2 (i) slash QQ_2$ is ramified.
]

#proof[
  For odd $p$, the polynomial $X^2+1$ has a root in $FF_p$ exactly when
  $p equiv 1 mod 4$. Such roots are simple and lift to $ZZ_p$, giving the
  product decomposition. If $p equiv 3 mod 4$, the reduction is irreducible,
  so $X^2+1$ remains irreducible over $QQ_p$ and its root generates a degree
  two extension. Its integer ring reduces to
  $FF_p[X] slash (X^2+1) tilde.eq FF_(p^2)$, so the residue degree is two and
  the ramification index is one. At $p=2$, the element $1+i$ satisfies

  $ (1+i)^2=2i, quad "N"_(QQ_2 (i) slash QQ_2) (1+i)=2 $

  so $1+i$ is a uniformizer and the quadratic extension is ramified.
]

#remark(title: "Connection with Earlier Splitting Theory")[
  Globally, the same congruence distinguishes split and inert primes in
  $QQ(i) slash QQ$. Locally, Hensel's lemma explains why the factorization of
  $X^2+1$ modulo $p$ persists after passing from $FF_p$ to $QQ_p$. The tensor
  product displays all branches above $p$ simultaneously.
]

=== Integrality from the Constant Term

The factorization form also controls coefficients of irreducible polynomials
over a complete discretely valued field.

#lemma(title: "Hensel--Kürschák Lemma")[
  Let $A$ be a complete DVR with fraction field $K$. If an irreducible
  polynomial $f in K[X]$ has its leading and constant coefficients in $A$,
  then every coefficient of $f$ lies in $A$.
]

#proof[
  Write $f=sum_(j=0)^n c_j X^j$ and let

  $ m:=min_(0<=j<=n) v(c_j) $

  Suppose $m<0$ and put $g=pi^(-m)f in A[X]$. Some coefficient of $g$ is a
  unit, while the leading and constant coefficients lie in $frak(m)$.
  Therefore $overline(g)$ has positive degree, zero constant term, and degree
  strictly less than $n$.

  Write

  $ overline(g)=X^d h_0 $

  where $d>=1$ is maximal. Then $X^d$ and $h_0$ are coprime, with
  $0<d<n$. The general factorization form lifts $X^d$ to a factor of $g$ of
  degree $d$, producing a nontrivial factorization of $g$, hence of $f$.
  This contradicts irreducibility. Thus $m>=0$ and $f in A[X]$.
]

#corollary(title: "A Norm Criterion for Integrality")[
  Let $L slash K$ be a finite extension, where $K$ is the fraction field of a
  complete DVR $A$. For $alpha in L$,

  $ alpha " is integral over " A <=> "N"_(L slash K) (alpha) in A $
]

#proof[
  If $alpha$ is integral, its minimal polynomial over $K$ lies in $A[X]$, so
  its constant term and hence the norm lie in $A$.

  Conversely, let $f in K[X]$ be the monic minimal polynomial of $alpha$ and
  put $e=[L:K(alpha)]$. Then

  $ "N"_(L slash K) (alpha)=(-1)^([L:K]) f(0)^e $

  If the norm belongs to $A$, the valuation gives $v(f(0))>=0$, so
  $f(0) in A$. The leading coefficient is $1 in A$, and the
  Hensel--Kürschák lemma implies $f in A[X]$. Hence $alpha$ is integral.
]

=== Exercises

+ #emph[Explicit cube root.] Starting from $a_1=3 mod 5$, use the one-digit
  Hensel step to compute the root of $X^3-2$ in $ZZ_5$ modulo
  $5^2,5^3$, and $5^4$.

+ #emph[Square classes.] Determine whether each of

  $ 2,3,5,6,10,-1 $

  is a square in $QQ_3$, $QQ_5$, and $QQ_7$.

+ #emph[Roots of unity.] Prove that $X^(p-1)-1$ has exactly $p-1$ roots in
  $ZZ_p$ and that reduction identifies them with $FF_p^times$. For odd $p$,
  deduce

  $ ZZ_p^times tilde.eq mu_(p-1) times (1+p ZZ_p) $

+ #emph[A fourth-root problem.] Find a necessary and sufficient congruence
  condition on an odd unit $u in ZZ_2^times$ for $u$ to be a fourth power in
  $QQ_2$.

+ #emph[Factor lifting.] Factor $X^4+1$ modulo $5$ into two coprime quadratic
  polynomials, and lift the factorization first to
  $(ZZ slash 25ZZ)[X]$ and then to $ZZ_5[X]$.

+ #emph[Irreducibility by reduction.] Let $f in cal(O)[X]$ be monic. Prove
  that if $overline(f)$ is irreducible over $kappa$, then $f$ is irreducible
  over $K$. Explain why the converse fails.

+ #emph[Why completion matters.] Show that $ZZ_((5))$ is not henselian by
  considering $X^2-6$. Compare this with the two roots that appear after
  passing to $ZZ_5$.

+ #emph[Étale lifting.] Let $A$ be henselian and let $f in A[X]$. Interpret
  the simple-root form as a bijection between simple roots of $f$ in $A$ and
  simple roots of $overline(f)$ in $A slash frak(m)$. Reformulate this as a
  statement about sections of an étale morphism over $Spec A$.

#remark(title: "Hints for the Exercises")[
  For the fourth-root problem, first square the criterion for squares in
  $QQ_2$ and keep one more level of congruence. For irreducibility, clear
  denominators in a hypothetical factorization and use the integrality of
  monic factors. For the henselian counterexample, note that $6$ has a simple
  square root modulo $5$ but no square root in $QQ$.
]
