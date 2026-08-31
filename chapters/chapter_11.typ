#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Global Fields

A global field is seen locally only after one chooses a notion of size. Unlike
a local field, it carries many inequivalent notions of size at once: ordinary
absolute values coming from embeddings into $CC$, and nonarchimedean absolute
values coming from prime ideals or closed points. A #emph[place] remembers one
such direction without committing to an arbitrary normalization.

#quote[
  A global field is one arithmetic object viewed from all of its places; a
  local field is what one sees after choosing one place and completing.
]

== Places of Fields

=== Places, Representatives, and Completions

Chapter 6 proved that two nontrivial absolute values induce the same topology
exactly when one is a positive power of the other. This is the equivalence
relation we now package into a single object.

#definition(title: "Place of a Field")[
  A #emph[place] $v$ of a field $K$ is an equivalence class of nontrivial
  absolute values on $K$. Thus

  $ abs(dot)_v tilde.eq abs(dot)_v' $

  if there is an $s>0$ such that

  $ abs(x)_v'=abs(x)_v^s quad "for every " x in K $

  The set of places of $K$ is denoted by $M_K$.
]

#remark(title: "Why a Place Is an Equivalence Class")[
  Replacing $abs(dot)_v$ by a positive power changes the numerical scale but
  not the open sets, Cauchy sequences, valuation ring, or completion. A place
  is therefore a direction of magnification rather than a choice of ruler.
]

#remark(title: "Another Use of the Word Place")[
  In valuation theory, a place may also mean a map

  $ K->kappa union {infinity} $

  compatible with field operations wherever they are defined. Such a map is
  obtained from a valuation ring by reduction to its residue field. In this
  chapter, however, #emph[place] always means an equivalence class of
  real-valued absolute values. For global fields these viewpoints carry the
  same prime-by-prime information.
]

#definition(title: "Archimedean and Nonarchimedean Places")[
  A place is #emph[archimedean] if one, hence every, representative is
  archimedean. Otherwise it is #emph[nonarchimedean]. We write

  $ M_K^infinity:={v in M_K | v " is archimedean"} $

  $ M_K^0:={v in M_K | v " is nonarchimedean"} $

  Thus $M_K=M_K^infinity union M_K^0$, and the union is disjoint.
  Archimedean places are also called #emph[infinite places]; nonarchimedean
  places are called #emph[finite places] when $K$ is a number field.
]

#definition(title: "Local Data at a Place")[
  Let $v in M_K$ and choose a representative $abs(dot)_v$. The
  #emph[completion of $K$ at $v$] is denoted by $K_v$. The canonical map

  $ K arrow.r.hook K_v $

  is isometric and has dense image.

  It is canonically determined as a topological field by the place $v$.

  If $v$ is nonarchimedean, define

  $ cal(O)_v:={x in K : abs(x)_v<=1} $

  $ frak(m)_v:={x in K : abs(x)_v<1} $

  $ kappa(v):=cal(O)_v slash frak(m)_v $

  These are respectively the valuation ring, its maximal ideal, and the
  residue field of $v$. Their completed analogues are the valuation ring
  $cal(O)_(K_v)$ and residue field of $K_v$.
]

#proposition(title: "The Local Data Do Not Depend on the Representative")[
  Equivalent absolute values determine the same completion, valuation ring,
  maximal ideal, and residue field.
]

#proof[
  If $abs(x)_v'=abs(x)_v^s$ with $s>0$, then

  $ abs(x)_v<=1 <=> abs(x)_v'<=1 $

  and similarly with strict inequality. This proves equality of the valuation
  rings and maximal ideals. The two absolute values have the same Cauchy and
  null sequences, so the construction of completion in Chapter 7 gives a
  canonical topological-field isomorphism between the completions.
]

#remark(title: "Places and Rank-One Valuations")[
  A nonarchimedean place is equivalently an equivalence class of rank-one
  valuations: after choosing $0<c<1$ one writes

  $ abs(x)_v=c^(v(x)) $

  Rescaling the additive valuation or changing $c$ changes the representative
  but not the place. For a global field every nonarchimedean place is discrete,
  so it has a normalized valuation

  $ v:K^times->ZZ $

  with value group exactly $ZZ$.
]

=== Archimedean Places of Number Fields

Let $K$ be a number field of degree $n$. Every embedding
$sigma:K->CC$ defines an absolute value

$ abs(x)_sigma:=abs(sigma(x)) $

Complex-conjugate embeddings define the same absolute value. These account
for every archimedean place.

#theorem(title: "Archimedean Places and Embeddings")[
  There is a canonical bijection

  $ M_K^infinity tilde.eq Hom_QQ (K,CC) slash (sigma tilde.eq overline(sigma)) $

  Under this bijection:

  + a #emph[real place] is represented by an embedding
    $sigma:K->RR$, and its completion is $K_v tilde.eq RR$;

  + a #emph[complex place] is represented by a pair
    ${sigma,overline(sigma)}$ of nonreal embeddings, and its completion is
    $K_v tilde.eq CC$.
]

#proof[
  Every embedding gives an archimedean absolute value by restriction of the
  usual modulus on $CC$. Conjugation does not change this modulus, so
  $sigma$ and $overline(sigma)$ give the same place.

  Conversely, let $v$ be archimedean. Its restriction to $QQ$ is equivalent
  to the usual absolute value by Ostrowski's theorem. After choosing the
  representative that restricts to the usual one, the completion $K_v$
  contains $RR$ and is a finite extension of $RR$. Hence

  $ K_v tilde.eq RR " or " CC $

  Embedding $K$ densely into $K_v$ and then into $CC$ produces the required
  field embedding.

  Finally, suppose two embeddings give equivalent absolute values. Their
  restrictions to $QQ$ are already normalized, so the exponent relating
  them is $1$. The identities

  $ abs(sigma(x))=abs(tau(x)), quad
    abs(1+sigma(x))=abs(1+tau(x)) $

  determine the real parts as well as the moduli. Thus
  $tau(x)$ equals either $sigma(x)$ or $overline(sigma(x))$; compatibility
  with addition and multiplication makes the choice uniform in $x$. Hence
  $tau=sigma$ or $tau=overline(sigma)$.
]

#definition(title: "Signature")[
  Let $r_1$ be the number of real places of $K$ and let $r_2$ be the number
  of complex places. The pair $(r_1,r_2)$ is the #emph[signature] of $K$.
  Since a real place represents one embedding and a complex place represents
  two,

  $ [K:QQ]=r_1+2r_2 $
]

#example(title: "Three Archimedean Patterns")[
  + The field $QQ$ has one real place.

  + The field $QQ(sqrt(5))$ has two real places, given by

    $ sqrt(5) mapsto sqrt(5), quad sqrt(5) mapsto -sqrt(5) $

    Its signature is $(2,0)$.

  + The field $QQ(i)$ has two embeddings into $CC$, but they are exchanged by
    complex conjugation. Thus it has one complex place and signature $(0,1)$.
]

#remark(title: "Geometric Points at Infinity")[
  The scheme $"Spec" cal(O)_K$ contains the nonzero prime ideals of
  $cal(O)_K$ as closed points, but it does not contain the real and complex
  embeddings. Arakelov geometry formally adjoins the archimedean places as
  points at infinity. This makes the finite and infinite directions of a
  number field part of one geometric object.
]

=== Finite Places of Number Fields

Let $cal(O)_K$ be the ring of integers of $K$. For every nonzero prime ideal
$frak(p) subset.eq cal(O)_K$, the prime-ideal factorization of a principal
fractional ideal defines the normalized discrete valuation

$ v_frak(p) (x):=v_frak(p) ((x)) $

for $x in K^times$.

#definition(title: "The Place Attached to a Prime Ideal")[
  Let

  $ "N"(frak(p)):=abs(cal(O)_K slash frak(p)) $

  be the absolute ideal norm. The formula

  $ norm(x)_frak(p):="N"(frak(p))^(-v_frak(p) (x)) $

  defines a nonarchimedean absolute value on $K$. Its place is denoted again
  by $frak(p)$. This representative is called the #emph[global
  normalization] at $frak(p)$.
]

#theorem(title: "Finite Places and Prime Ideals")[
  The assignment $frak(p) mapsto [norm(dot)_frak(p)]$ is a canonical
  bijection

  $ {0!=frak(p) in "Spec" cal(O)_K}
    tilde.eq M_K^0 $

  Under this correspondence,

  $ cal(O)_frak(p)=(cal(O)_K)_frak(p) $

  $ frak(m)_frak(p)=frak(p)(cal(O)_K)_frak(p) $

  $ kappa(frak(p))=cal(O)_K slash frak(p) $

  and $K_frak(p)$ is a finite extension of $QQ_p$, where
  $p=frak(p) inter ZZ$.
]

#proof[
  The valuation identities make $norm(dot)_frak(p)$ a nonarchimedean
  absolute value, and its unit ball consists exactly of the elements
  $x in K$ with $v_frak(p) (x)>=0$. This is the DVR
  $(cal(O)_K)_frak(p)$, giving the displayed local data.

  Conversely, let $v$ be a nonarchimedean place of $K$. Its restriction to
  $QQ$ cannot be trivial. Indeed, an absolute value trivial on $QQ$ remains
  trivial on every finite algebraic extension: in a minimal polynomial, a
  uniquely largest term cannot cancel. Ostrowski's theorem therefore gives a
  unique rational prime $p$ below $v$. The set

  $ frak(p):={a in cal(O)_K | abs(a)_v<1} $

  is a nonzero prime ideal above $p$. Its localization is the valuation ring
  of $v$, so $v$ is the place defined by $v_frak(p)$. Distinct prime ideals
  give distinct valuation rings and hence distinct places.

  Finally, completing $K$ at this extension of the $p$-adic place produces a
  finite extension of $QQ_p$, as proved in Chapters 8 and 9.
]

#remark(title: "Closed Points and Finite Places")[
  The bijection may be written geometrically as

  $ M_K^0 tilde.eq ("Spec" cal(O)_K)^((1)) $

  The right-hand side is the set of closed, or codimension-one, points of the
  arithmetic curve $"Spec" cal(O)_K$. Completing at $frak(p)$ means zooming
  into the formal neighborhood of this closed point.
]

#example(title: [Places of $QQ$])[
  Ostrowski's theorem gives

  $ M_QQ={infinity,2,3,5,7,dots} $

  The infinite place is represented by the ordinary absolute value and has
  completion $QQ_infinity=RR$. The place $p$ is represented by
  $abs(dot)_p$ and has completion $QQ_p$.
]

#example(title: "Places of the Gaussian Field")[
  The field $K=QQ(i)$ has one complex place. Its finite places are the nonzero
  prime ideals of $ZZ[i]$. Above an odd rational prime $p$:

  + if $p equiv 1 mod 4$, there are two places above $p$;

  + if $p equiv 3 mod 4$, there is one place above $p$;

  + above $2$ there is one ramified place, represented by $(1+i)$.

  Thus splitting of prime ideals is exactly splitting of finite places.
]

=== Places of Global Function Fields

Let $K$ be a global function field with full constant field $FF_q$. Choose
the smooth projective geometrically integral curve $C slash FF_q$ whose
function field is $K$.

#theorem(title: "Places as Closed Points of a Curve")[
  There are canonical bijections

  $ M_K tilde.eq {"normalized discrete valuations of " K " trivial on " FF_q}
    tilde.eq {"closed points of " C} $

  For a closed point $x in C$, the corresponding valuation is the order of
  vanishing

  $ "ord"_x:K^times->ZZ $

  its valuation ring is the local ring $cal(O)_(C,x)$, and its residue field
  is the finite extension $kappa(x) slash FF_q$.
]

#proofsketch[
  A nonzero rational function on a regular curve has a well-defined order of
  zero or pole at every closed point, giving a normalized discrete valuation.
  Conversely, the center of a discrete valuation trivial on $FF_q$ is a
  unique closed point on the proper curve $C$. Regularity identifies the
  valuation ring with the local ring at that point. Since $C$ is of finite
  type over the finite field, every closed-point residue field is finite.
]

#definition(title: "Degree and Normalization of a Function-Field Place")[
  For a place $x in M_K$, define

  $ deg(x):=[kappa(x):FF_q] $

  A convenient representative of the place is

  $ norm(f)_x:=q^(-deg(x) "ord"_x(f)) $

  The completion $K_x$ is a nonarchimedean local field with residue field
  $kappa(x)$; after choosing a uniformizer $pi_x$,

  $ K_x tilde.eq kappa(x)((pi_x)) $
]

#remark(title: "There Are No Archimedean Function-Field Places")[
  Every absolute value on the finite constant field $FF_q$ is trivial, and
  every place of $K$ is nonarchimedean. A point called “infinity” on a
  projective curve is therefore not an archimedean place; it is an ordinary
  closed point selected by an affine presentation.
]

#example(title: [The Places of $FF_q (t)$])[
  The finite closed points of $AA^1_(FF_q)$ correspond to monic irreducible
  polynomials $P(t) in FF_q [t]$. They give valuations

  $ v_P (f slash g)="ord"_P (f)-"ord"_P (g) $

  The projective line has one additional point $infinity$, with

  $ v_infinity (f slash g)=deg(g)-deg(f) $

  Hence

  $ M_(FF_q (t))={v_P:P " monic irreducible"} union {v_infinity} $

  All these places are nonarchimedean. The phrase “place at infinity” refers
  only to the missing point in the affine coordinate $t$.
]

=== Restricting and Extending Places

#definition(title: "A Place Lying Above Another")[
  Let $L slash K$ be an extension of fields, let $w in M_L$, and let
  $v in M_K$. We say that $w$ #emph[lies above] $v$, and write $w|v$, if the
  restriction of a representative of $w$ to $K$ belongs to the place $v$.
]

#proposition(title: "Places above a Place")[
  Let $L slash K$ be a finite extension of global fields.

  + Every place $w$ of $L$ restricts to a unique place $v$ of $K$.

  + Every place $v$ of $K$ has at least one and only finitely many places of
    $L$ above it.

  + For every $w|v$, the inclusion $K->L$ extends continuously to a finite
    extension of local fields

    $ K_v->L_w $
]

#proof[
  Restriction of an absolute value gives an absolute value on $K$. It cannot
  become trivial because $L slash K$ is algebraic: an element of $L$ is
  controlled by its minimal polynomial over $K$. Hence the restricted place
  is unique.

  At a nonarchimedean place, the assertion becomes the factorization of a
  prime of the integral closure into finitely many primes. At an archimedean
  place, it becomes the finite problem of extending an embedding
  $K->CC$ to $L$. In both cases at least one extension exists. Continuity and
  the universal property of completion then extend $K->L$ to
  $K_v->L_w$; finite-dimensionality survives completion.
]

#theorem(title: "The Local Decomposition of a Global Extension")[
  Let $L slash K$ be finite separable and let $v in M_K$. Then

  $ L ⊗_K K_v tilde.eq product_(w|v) L_w $

  In particular,

  $ sum_(w|v) [L_w:K_v]=[L:K] $

  If $v$ is nonarchimedean, then

  $ [L_w:K_v]=e_(w slash v) f_(w slash v) $

  and therefore

  $ sum_(w|v) e_(w slash v)f_(w slash v)=[L:K] $
]

#proof[
  Write $L=K(alpha)$ and let $f$ be the separable minimal polynomial of
  $alpha$. Factor it over the complete field $K_v$:

  $ f=f_1 dots f_r $

  into distinct monic irreducible factors. The Chinese remainder theorem
  gives

  $ L ⊗_K K_v
    tilde.eq K_v [X] slash (f)
    tilde.eq product_(i=1)^r K_v [X] slash (f_i) $

  Each factor is the completion $L_w$ for one place $w|v$. Taking dimensions
  over $K_v$ proves the degree sum. In the nonarchimedean case, the local
  degree formula from Chapter 9 gives $[L_w:K_v]=e_(w slash v)f_(w slash v)$.
]

#corollary(title: "Places above a Place as Galois Orbits of Embeddings")[
  Let $L slash K$ be a finite separable extension of global fields, let
  $v in M_K$, and fix an algebraic closure $overline(K_v)$ of $K_v$. There is
  a canonical bijection

  $ Hom_K (L,overline(K_v)) slash "Gal"(overline(K_v) slash K_v)
    tilde.eq {w in M_L | w|v} $

  Here $"Gal"(overline(K_v) slash K_v)$ acts on the set of $K$-embeddings by
  postcomposition:

  $ gamma dot iota:=gamma compose iota $

  Thus the places of $L$ above $v$ are precisely the absolute-local-Galois
  orbits of embeddings of $L$ into $overline(K_v)$.
]

#proof[
  By the primitive element theorem, write

  $ L=K(alpha) tilde.eq K[X] slash (f) $

  with $f in K[X]$ the separable minimal polynomial of $alpha$. Evaluation at
  $alpha$ gives an equivariant bijection

  $ Hom_K (L,overline(K_v))
    tilde.eq {beta in overline(K_v) | f(beta)=0} $

  where the absolute Galois group acts on the right by acting on roots.

  Factor $f$ over $K_v$ as

  $ f=f_1 dots f_r $

  with the $f_i in K_v[X]$ distinct, monic, and irreducible. The group
  $"Gal"(overline(K_v) slash K_v)$ acts transitively on the roots of each
  $f_i$, and roots belonging to different irreducible factors cannot lie in
  the same orbit. Hence its orbits on the roots of $f$ are in bijection with
  the irreducible factors $f_1,dots,f_r$.

  The local decomposition theorem identifies these factors with the factors

  $ K_v[X] slash (f_i)=L_w $

  of $L ⊗_K K_v$, and those factors are indexed by the places $w|v$. Composing
  the two correspondences gives the claimed bijection.

  More intrinsically, an embedding $iota:L->overline(K_v)$ pulls the unique
  extension of $v$ on $overline(K_v)$ back to a place of $L$. Postcomposition
  by an element of the absolute Galois group does not change this pulled-back
  place, which shows that the bijection is independent of the chosen
  primitive element.
]

#remark(title: "Splitting Is a Statement about Places")[
  A place $v$ does not become one mysterious larger place in $L$. It splits
  into the finite family ${w:w|v}$, and the completed algebra separates these
  branches as a product. For finite places this recovers prime-ideal
  factorization; for archimedean places it records how real embeddings stay
  real or pair up to become complex.
]

#remark(title: [Local Degrees over $QQ$])[
  For a number field $K$ and a place $v$ above a place $u$ of $QQ$, put

  $ n_v:=[K_v:QQ_u] $

  Thus $n_v=1$ at a real place, $n_v=2$ at a complex place, and
  $n_v=e_v f_v$ at a finite place. The local decomposition theorem gives

  $ sum_(v|u) n_v=[K:QQ] $

  These local degrees are the weights that later make global product formulas
  treat real, complex, and $p$-adic places uniformly.
]

#block(breakable: false)[
  #align(center, table(
    columns: (1.05fr, 1.25fr, 1.15fr, 1.2fr),
    align: (left, center, center, left),
    inset: (x: 8pt, y: 5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[Global place]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Representative]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Completion]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Geometric point]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    [real], [$abs(sigma(x))$], [$RR$], [point at infinity],
    [complex], [$abs(sigma(x))$], [$CC$], [conjugate pair at infinity],
    [number-field finite], [$"N"(frak(p))^(-v_frak(p) (x))$], [$K_frak(p)$], [$frak(p) in "Spec" cal(O)_K$],
    [function-field], [$q^(-deg(x) "ord"_x(f))$], [$K_x$], [$x in C^((1))$],
  ))
]

#remark(title: "Can All Places Be Viewed as Points?")[
  For a global function field the answer is literally yes. There is a unique
  smooth projective geometrically integral curve $C slash FF_q$ with function
  field $K$, and

  $ M_K tilde.eq {"closed points of " C} $

  Properness is what prevents a valuation from disappearing at infinity: every
  place has a center on $C$.

  For a number field, ordinary scheme theory gives only

  $ M_K^0 tilde.eq ("Spec" cal(O)_K)^((1)) $

  The archimedean places are not prime ideals and therefore are not points of
  the scheme $"Spec" cal(O)_K$. Arakelov geometry nevertheless forms a
  generalized compactification, written symbolically as

  $ overline("Spec" cal(O)_K)^"Ar"
    ="Spec" cal(O)_K union M_K^infinity $

  One should regard this as an #emph[arithmetic curve with points at infinity],
  not as an ordinary scheme obtained merely by adjoining more prime ideals.
  In this enlarged geometry, the product formula becomes the analogue of the
  statement that every principal divisor on a proper algebraic curve has
  degree zero.
]

#quote[
  A place is the interface between global arithmetic and local analysis:
  restrict to one notion of size, complete, and the global field becomes a
  local field.
]

== Locally Compact Abelian Groups and Harmonic Analysis

Passing from a global field $K$ to a completion $K_v$ does more than produce a
topological field. Its additive group becomes locally compact, so it carries a
translation-invariant notion of volume. This is the point at which local
arithmetic meets harmonic analysis.

=== Haar Measure

#definition(title: "Locally Compact Abelian Group")[
  A #emph[locally compact abelian group], abbreviated #emph[LCA group], is a
  Hausdorff topological abelian group $G$ in which every point has a compact
  neighborhood. We use additive notation, with identity $0$.
]

#example(title: "Basic LCA Groups")[
  The following groups will occur repeatedly.

  + The groups $RR^n$ and $CC^n$ are LCA groups under addition.
  + Every discrete abelian group is locally compact: each singleton is a
    compact open set.
  + Every compact abelian group is an LCA group.
  + The additive group of every local field $F$ is an LCA group. If $F$ is
    nonarchimedean, its valuation ring $cal(O)_F$ is a compact open subgroup.
  + Finite products of LCA groups are LCA groups.
]

#definition(title: "Radon and Haar Measures")[
  Let $G$ be an LCA group, and let $cal(B)(G)$ be its Borel $sigma$-algebra. A
  Borel measure $mu$ on $G$ is a #emph[Radon measure] if it is finite on compact
  sets, outer regular on Borel sets, and inner regular on open sets.

  A #emph[Haar measure] on $G$ is a nonzero Radon measure $mu_G$ that is
  translation invariant:

  $ mu_G (x+E)=mu_G (E) quad (x in G, E in cal(B)(G)) $

  Equivalently, for every $f in C_c (G)$ and $x in G$,

  $ integral_G f(x+y) dif mu_G (y)=integral_G f(y) dif mu_G (y) $
]

The Radon conditions are not decorative technicalities. Finiteness on compact
sets makes compactly supported functions integrable, while regularity lets us
recover the measure from those functions. The space $C_c(G)$ is therefore the
natural testing ground for Haar measure.

#theorem(title: "Haar Existence Theorem")[
  Every locally compact Hausdorff group admits a nonzero left-invariant Radon
  measure. In particular, every LCA group admits a Haar measure.
]

#proofsketch[
  Choose a nonzero function $phi in C_c (G)$ with $phi>=0$. Local compactness
  implies that a compact set can be covered by finitely many translates of
  the open set on which $phi$ is positive. These finite covering numbers give
  normalized positive functionals on $C_c(G)$.

  By passing to a convergent subnet, one obtains a nonzero positive linear
  functional $I:C_c(G)->RR$ satisfying

  $ I(f(x+dot))=I(f) $

  The Riesz--Markov representation theorem writes this functional uniquely as

  $ I(f)=integral_G f dif mu_G $

  for a Radon measure $mu_G$. The invariance of $I$ becomes translation
  invariance of $mu_G$. The compactness argument is the technical heart of the
  proof; conceptually, it constructs volume by averaging away the choice of
  origin.
]

#theorem(title: "Haar Uniqueness Theorem")[
  If $mu_G$ and $nu_G$ are Haar measures on an LCA group $G$, then there is a
  unique constant $c>0$ such that

  $ nu_G=c mu_G $
]

#proofsketch[
  Integration against the two measures gives positive translation-invariant
  functionals $I_mu,I_nu:C_c (G)->CC$. The Haar comparison lemma says that for
  every nonzero $phi in C_c (G)$ with $phi>=0$ and every $f in C_c (G)$,

  $ I_nu (f) I_mu (phi)=I_mu (f) I_nu (phi) $

  To prove the comparison lemma, approximate a nonnegative compactly supported
  function from above and below by finite sums of small translates of $phi$.
  Translation invariance makes the value of every translate equal; regularity
  makes the two approximations converge to the same value. Hence

  $ I_nu (f)=c I_mu (f), quad c:=I_nu (phi) slash I_mu (phi)>0 $

  The Riesz--Markov uniqueness theorem now gives $nu_G=c mu_G$. The constant
  is unique because $mu_G$ is nonzero.
]

#quote[
  Existence says that an LCA group has a translation-invariant ruler;
  uniqueness says that the only remaining choice is its unit of volume.
]

#corollary(title: "Canonical Normalizations in the Basic Cases")[
  Haar uniqueness gives the following standard normalizations.

  + On a discrete group, normalize by $mu_G ({0})=1$. The resulting Haar
    measure is counting measure.
  + On a compact group, normalize by $mu_G (G)=1$. The resulting Haar measure
    is a probability measure.
  + On $RR^n$, Lebesgue measure is Haar measure.
  + On a nonarchimedean local field $F$, normalize additive Haar measure by

    $ mu_F (cal(O)_F)=1 $
]

#remark(title: "Products and Quotients")[
  The product of Haar measures is Haar measure on a finite product. If $H$ is
  a closed subgroup of $G$, Haar measures on $H$ and $G$ determine a compatible
  Haar measure on $G slash H$, up to the expected scalar. With compatible
  normalizations, Weil's integration formula is

  $ integral_G f(x) dif mu_G (x)
    =integral_(G slash H) integral_H f(x+h) dif mu_H (h)
      dif mu_(G slash H) (x+H) $

  Thus integration over $G$ can be performed first along the fibers of
  $G->G slash H$ and then over the quotient. This is the measure-theoretic
  analogue of integrating a function fiber by fiber in geometry.
]

=== The Modulus of an Automorphism

Haar measure is translation invariant, but it need not be invariant under an
arbitrary automorphism of the group. Uniqueness determines exactly how volume
changes.

#proposition(title: "Modulus of an Automorphism")[
  Let $alpha:G->G$ be a topological automorphism of an LCA group. There is a
  unique number $mod_G (alpha)>0$ such that

  $ mu_G (alpha(E))=mod_G (alpha) mu_G (E) $

  for every Borel set $E$. It is independent of the chosen Haar measure, and

  $ mod_G (alpha compose beta)=mod_G (alpha) mod_G (beta) $
]

#proof[
  The assignment $E mapsto mu_G (alpha(E))$ is again a Haar measure on $G$.
  Haar uniqueness therefore makes it a positive scalar multiple of $mu_G$.
  Replacing $mu_G$ by $c mu_G$ does not change this scalar, and applying the
  formula successively to $beta$ and $alpha$ proves multiplicativity.
]

#remark(title: "The Modulus as a Character of the Automorphism Group")[
  Write $"Aut"(G)$ for the group of topological automorphisms of $G$. The
  proposition is equivalently the statement that change of Haar volume is a
  group homomorphism

  $ mod_G:"Aut"(G)->RR_(>0)^times $

  In other words, $mod_G$ is a positive real-valued character of the
  automorphism group. Its kernel

  $ ker(mod_G)={alpha in "Aut"(G) | mu_G (alpha(E))=mu_G (E)
    " for every Borel set " E} $

  is precisely the subgroup of #emph[volume-preserving automorphisms]. Thus
  $mod_G$ forgets the shape of an automorphism and remembers only its
  one-dimensional effect on volume.

  For example, if $G=RR^n$ and $A in "GL"_n (RR)$, then

  $ mod_G (A)=abs(det A) $

  If $G=F^n$ for a local field $F$, then similarly

  $ mod_G (A)=norm(det A)_F $

  The local modulus on $F^times$ is the pullback of this character along the
  multiplication representation

  $ F^times->"Aut"(F,+), quad a mapsto (x mapsto a x) $

  Hence $norm(dot)_F$ is not an extra function invented for local fields: it
  is the automorphism modulus of their additive LCA group.
]

#definition(title: "The Canonical Modulus of a Local Field")[
  Let $F$ be a local field. Multiplication by $a in F^times$ is an automorphism
  of the additive LCA group of $F$. Its modulus is denoted by

  $ norm(a)_F:=mod_(F,+)(x mapsto a x) $

  Thus, for additive Haar measure $mu_F$,

  $ mu_F (a E)=norm(a)_F mu_F (E) $
]

#proposition(title: "Calculation of the Local Modulus")[
  The canonical modulus is given by

  $ norm(a)_RR=abs(a), quad norm(a)_CC=abs(a)^2 $

  If $F$ is nonarchimedean, $v_F$ is normalized by
  $v_F (pi_F)=1$, and the residue field has cardinality $q_F$, then

  $ norm(a)_F=q_F^(-v_F (a)) $
]

#proof[
  On $RR$, multiplication by $a$ scales length by $abs(a)$. On $CC tilde.eq
  RR^2$, it scales both real directions by $abs(a)$ and therefore scales area
  by $abs(a)^2$.

  Now suppose $F$ is nonarchimedean and normalize
  $mu_F (cal(O)_F)=1$. The ring $cal(O)_F$ is the disjoint union of $q_F$
  cosets of $pi_F cal(O)_F$. Translation invariance gives

  $ 1=mu_F (cal(O)_F)=q_F mu_F (pi_F cal(O)_F) $

  Hence $norm(pi_F)_F=q_F^(-1)$. Every $a in F^times$ has the form
  $a=u pi_F^n$ with $u in cal(O)_F^times$. Multiplication by $u$ preserves
  $cal(O)_F$, so $norm(u)_F=1$, and multiplicativity completes the proof.
]

#remark(title: "Why the Complex Place Has Weight Two")[
  A place remembers an absolute value only up to a positive power, but Haar
  measure chooses the scale relevant to volume. At a complex place, multiplication
  by $z$ scales two real dimensions, so the canonical local factor is
  $abs(z)^2$, not $abs(z)$. This is the analytic origin of the local degree
  $n_v=2$ that appeared above.

  Notice that $z mapsto abs(z)^2$ is a multiplicative modulus but is not an
  absolute value in the triangle-inequality sense. Its role is to measure
  change of volume.
]

#definition(title: "Multiplicative Haar Measure on a Local Field")[
  Since $F^times$ is also an LCA group, it has a multiplicative Haar measure.
  In terms of additive Haar measure it has the form

  $ dif^times x=c (dif mu_F (x)) slash norm(x)_F $

  for some $c>0$. In the nonarchimedean case one usually chooses $c$ so that

  $ mu_F^times (cal(O)_F^times)=1 $

  The factor $norm(x)_F^(-1)$ exactly cancels the change of additive volume
  under multiplication.
]

=== Convolution and Fourier Transform

Translation-invariant measure allows functions on $G$ to be averaged without
choosing an origin. The basic operation combining two such functions is
convolution.

#definition(title: "Convolution")[
  Let $G$ be an LCA group with Haar measure $mu_G$. For
  $f,g in L^1(G)$, their #emph[convolution] is

  $ (f ast g)(x):=integral_G f(y) g(x-y) dif mu_G (y) $

  wherever the integral is defined.
]

#proposition(title: "The Convolution Algebra")[
  If $f,g in L^1(G)$, then $f ast g in L^1(G)$ and

  $ norm(f ast g)_1<=norm(f)_1 norm(g)_1 $

  Convolution is associative and, because $G$ is abelian, commutative. Thus
  $L^1(G)$ is a commutative Banach algebra under convolution.
]

#proof[
  Tonelli's theorem and translation invariance give

  $ integral_G abs((f ast g)(x)) dif mu_G (x)
    <=integral_G integral_G abs(f(y)) abs(g(x-y))
      dif mu_G (y) dif mu_G (x)
    =norm(f)_1 norm(g)_1 $

  Associativity follows from Fubini's theorem. The substitution $y mapsto
  x-y$ proves commutativity.
]

#example(title: "Convolution on a Nonarchimedean Local Field")[
  Let $F$ be nonarchimedean and normalize $mu_F (cal(O)_F)=1$. If
  $1_(cal(O)_F)$ denotes the indicator function of $cal(O)_F$, then

  $ 1_(cal(O)_F) ast 1_(cal(O)_F)=1_(cal(O)_F) $

  Indeed, for fixed $x$, the integrand is $1$ exactly when
  $y in cal(O)_F inter (x-cal(O)_F)$. This intersection is
  $cal(O)_F$ if $x in cal(O)_F$ and is empty otherwise. Compact open
  subgroups therefore behave like idempotent averaging operators.
]

#definition(title: "Characters and the Pontryagin Dual")[
  A #emph[continuous character] of an LCA group $G$ is a continuous
  homomorphism

  $ chi:G->S^1:={z in CC : abs(z)=1} $

  The #emph[Pontryagin dual] of $G$ is the group

  $ hat(G):="Hom"_"cont" (G,S^1) $

  under pointwise multiplication, equipped with the compact-open topology.
  It is again an LCA group.
]

#definition(title: "Fourier Transform")[
  Fix Haar measure $mu_G$ on $G$. For $f in L^1(G)$, its #emph[Fourier
  transform] is the function on $hat(G)$ defined by

  $ hat(f)(chi):=integral_G f(x) overline(chi(x)) dif mu_G (x) $

]

The character $chi$ is a pure frequency: translating $x$ adds only the phase
$chi(x)$. The Fourier transform records how much of each frequency occurs in
$f$. A direct application of Fubini's theorem gives the central computational
rule

$ hat(f ast g)=hat(f) hat(g) $

Thus convolution, which is an integral operation on $G$, becomes pointwise
multiplication on its dual.

#theorem(title: "Basic Fourier Theorems on an LCA Group")[
  Let $G$ be an LCA group.

  + #emph[Riemann--Lebesgue.] If $f in L^1(G)$, then $hat(f)$ is continuous
    and vanishes at infinity on $hat(G)$.
  + #emph[Fourier inversion.] The Haar measure on $hat(G)$ can be normalized
    so that, whenever $f$ and $hat(f)$ are integrable and $f$ is continuous,

    $ f(x)=integral_(hat(G)) hat(f)(chi) chi(x) dif mu_(hat(G)) (chi) $

  + #emph[Plancherel.] With this compatible normalization, Fourier transform
    extends uniquely to a unitary map

    $ L^2(G) tilde.eq L^2(hat(G)) $
]

#remark(title: "Normalization Is Part of Fourier Inversion")[
  Scaling $mu_G$ rescales $hat(f)$, so the dual Haar measure must be rescaled
  inversely for the inversion formula to remain true. A nontrivial additive
  character on a local field selects a particularly useful #emph[self-dual
  measure]. The measure, the character, and the Fourier-transform convention
  should therefore always be specified together.
]

=== Pontryagin Duality

The dual group is not merely a convenient set of test functions: taking
characters twice recovers the original topological group.

#theorem(title: "Pontryagin Duality")[
  For every LCA group $G$, the evaluation map

  $ "ev"_G:G->hat(hat(G)), quad x mapsto (chi mapsto chi(x)) $

  is an isomorphism of topological groups.
]

#example(title: "The Basic Dual Pairs")[
  With the usual topologies,

  $ hat(RR^n) tilde.eq RR^n, quad hat(ZZ) tilde.eq S^1,
    quad hat(S^1) tilde.eq ZZ $

  The first isomorphism sends $xi in RR^n$ to

  $ x mapsto exp(2 pi i x dot xi) $

  A finite abelian group has a dual of the same cardinality. It is isomorphic
  to its dual, although generally not by a canonical isomorphism.
]

#corollary(title: "Compact and Discrete Are Dual Notions")[
  An LCA group $G$ is compact if and only if $hat(G)$ is discrete, and $G$ is
  discrete if and only if $hat(G)$ is compact.
]

#definition(title: "Annihilators")[
  For a closed subgroup $H subset.eq G$, its #emph[annihilator] is

  $ H^perp:={chi in hat(G) | chi(h)=1 " for every " h in H} $

  Pontryagin duality identifies

  $ hat(G slash H) tilde.eq H^perp, quad
    hat(H) tilde.eq hat(G) slash H^perp $

  Thus passing to a quotient on one side becomes passing to a subgroup on the
  dual side.
]

#example(title: "Additive Self-Duality of a Local Field")[
  Let $F$ be a local field and choose a nontrivial continuous additive
  character $psi:F->S^1$. Then

  $ F->hat(F), quad a mapsto (x mapsto psi(a x)) $

  is a topological isomorphism. The isomorphism depends on $psi$, so the
  additive group of $F$ is self-dual but not canonically self-dual without a
  chosen character.

  If $H subset.eq F$ is a compact open additive subgroup, then

  $ hat(1_H)=mu_F (H) 1_(H^perp) $

  For $F=QQ_p$, choose the standard character whose kernel is $ZZ_p$ and the
  self-dual measure with $mu_F (ZZ_p)=1$. Then $ZZ_p^perp=ZZ_p$, and hence

  $ hat(1_(ZZ_p))=1_(ZZ_p) $

  This tiny formula is the nonarchimedean analogue of the special role played
  by Gaussian functions in real Fourier analysis.
]

#quote[
  Haar measure makes translation measurable, convolution combines local
  averages, and Pontryagin duality turns those averages into multiplication
  by frequencies.
]

== The Product Formula and the Definition of Global Fields

We have so far used the classical meaning of #emph[global field]: a number
field or a function field of one variable over a finite field. Haar measure
now reveals a more intrinsic meaning. A global field is a field whose local
views are local fields and whose local notions of volume satisfy one global
conservation law.

=== Normalized Local Moduli

#definition(title: "Normalized Local Modulus at a Place")[
  Let $K$ be a field, let $v in M_K$, and suppose that the completion $K_v$ is
  a local field. For $x in K_v^times$, choose additive Haar measure $mu_v$ on
  $K_v$ and a measurable set $S subset.eq K_v$ with
  $0<mu_v (S)<infinity$. Define

  $ norm(x)_v:=mu_v (x S) slash mu_v (S) $

  and put $norm(0)_v:=0$. This is the #emph[normalized local modulus] at $v$.
]

#proposition(title: "The Definition Is Intrinsic")[
  The number $norm(x)_v$ is independent of both $mu_v$ and $S$. It is a
  continuous homomorphism

  $ norm(dot)_v:K_v^times->RR_(>0)^times $

  and is the pullback of the automorphism modulus along

  $ K_v^times->"Aut"(K_v,+), quad x mapsto (y mapsto x y) $

  If $abs(dot)_v$ is any absolute value representing the place $v$, then

  $ norm(x)_v=abs(x)_v^m_v $

  for some $m_v>0$ independent of $x$.
]

#proof[
  The previous section gives

  $ mu_v (x S)=mod_(K_v,+)(y mapsto x y) mu_v (S) $

  for every measurable $S$ of finite nonzero measure. This proves independence
  of $S$, while Haar uniqueness proves independence of the normalization of
  $mu_v$. Multiplicativity and continuity come from the automorphism modulus.
  Finally, the classification of local fields gives $norm(x)_v=abs(x)$ on
  $RR$, $norm(x)_v=abs(x)^2$ on $CC$, and
  $norm(x)_v=q_v^(-v(x))$ in the nonarchimedean case. Every absolute value
  representing the same place is a positive power of the corresponding
  standard absolute value, which proves the final assertion.
]

#remark(title: "Modulus versus Absolute Value")[
  The term #emph[normalized absolute value] is also standard for
  $norm(dot)_v$. At a complex place, however,

  $ norm(z)_v=abs(z)^2 $

  which does not satisfy the ordinary triangle inequality. The term
  #emph[modulus] is more literal: $norm(z)_v$ measures the change of
  two-dimensional real volume under multiplication by $z$.
]

#example(title: "The Three Local Formulas")[
  The normalized local modulus is

  $ norm(x)_v=
    cases(
      abs(x) & K_v tilde.eq RR,
      abs(x)^2 & K_v tilde.eq CC,
      q_v^(-v(x)) quad & K_v " nonarchimedean with residue field " FF_(q_v)
    ) $
]

=== The Product Formula

#lemma(title: "Compatibility with the Local Field Norm")[
  Let $E slash F$ be a finite extension of local fields. For $x in E$,

  $ norm(x)_E=norm("N"_(E slash F) (x))_F $
]

#proof[
  For $CC slash RR$, this is the identity
  $abs(z)^2=abs(z overline(z))$. The other archimedean cases are immediate.
  In the nonarchimedean case, let the residue degree be $f$. Then

  $ v_F ("N"_(E slash F) (x))=f v_E (x), quad q_E=q_F^f $

  and therefore

  $ norm("N"_(E slash F) (x))_F
    =q_F^(-f v_E (x))=q_E^(-v_E (x))=norm(x)_E $
]

#theorem(title: "Product Formula")[
  Let $K$ be a number field or a global function field. For every
  $x in K^times$, one has $norm(x)_v=1$ at all but finitely many places and

  $ product_(v in M_K) norm(x)_v=1 $
]

#proof[
  We first consider the two rational global fields. If
  $x in QQ^times$, write $x=plus.minus product_p p^(v_p (x))$. Then

  $ norm(x)_infinity product_p norm(x)_p
    =abs(x) product_p p^(-v_p (x))=1 $

  Only the primes occurring in the numerator or denominator contribute.

  Now let $x=f slash g in FF_q (t)^times$ with $f,g in FF_q [t]$ coprime. The
  finite places are indexed by monic irreducible polynomials $P$, and the place
  at infinity satisfies $norm(x)_infinity=q^(deg f-deg g)$. Hence

  $ product_v norm(x)_v
    =q^(deg f-deg g)
      product_P q^(-deg(P) ("ord"_P (f)-"ord"_P (g)))=1 $

  because the degree of a polynomial is the sum of the degrees of its
  irreducible factors, counted with multiplicity.

  For the general case, choose a finite separable extension $K slash k$, where
  $k=QQ$ in characteristic zero and $k tilde.eq FF_q (t)$ in positive
  characteristic. For each place $u$ of $k$, the local decomposition theorem
  gives

  $ K ⊗_k k_u tilde.eq product_(v|u) K_v $

  Taking determinants of multiplication by $x$ and using the preceding lemma
  yields

  $ norm("N"_(K slash k) (x))_u=product_(v|u) norm(x)_v $

  Multiplying this equality over $u in M_k$ reduces the claim to the product
  formula for $k$.
]

#remark(title: "The Logarithmic and Divisor Viewpoints")[
  Taking logarithms turns the product formula into the additive relation

  $ sum_(v in M_K) log norm(x)_v=0 $

  Since $norm(x)_v=1$ for almost every $v$, this sum defines a finite
  $RR$-linear combination of places:

  $ D_"log" (x):=-sum_(v in M_K) log norm(x)_v [v] $

  Thus logarithm turns a global element into a #emph[logarithmic principal
  divisor] on $M_K$. Multiplicativity of the local moduli gives a group
  homomorphism

  $ D_"log":K^times->"Div"_RR (M_K), quad
    D_"log" (x y)=D_"log" (x)+D_"log" (y) $

  If the degree of $sum_v a_v [v]$ is defined to be $sum_v a_v$, then the
  product formula says exactly

  $ deg D_"log" (x)=0 $

  For a global function field, the underlying integral principal divisor is

  $ "div"(x)=sum_(P in C^((1))) "ord"_P (x)[P] $

  and the logarithmic coefficients encode its degree weights because

  $ -log norm(x)_P=log(q) deg(P) "ord"_P (x) $

  Consequently,

  $ deg("div"(x))=sum_(P in C^((1))) "ord"_P (x) deg(P)=0 $

  Thus a rational function has as many zeros as poles when multiplicities and
  residue-field degrees are counted.

  For a number field, the conventional #emph[Arakelov principal divisor] keeps
  integral orders at the finite places and logarithmic coefficients at
  infinity:

  $ "div"_"Ar" (x)
    :=sum_(frak(p) in M_K^0) v_frak(p) (x)[frak(p)]
      -sum_(v in M_K^infinity) log norm(x)_v [v] $

  Its degree is defined by

  $ deg_"Ar" lr((sum_frak(p) n_frak(p)[frak(p)]+sum_(v|infinity) a_v [v]))
    :=sum_frak(p) n_frak(p) log "N"(frak(p))+sum_(v|infinity) a_v $

  Since $log norm(x)_frak(p)=-v_frak(p) (x)log "N"(frak(p))$, the product
  formula is precisely

  $ deg_"Ar" ("div"_"Ar" (x))=0 $

  This is the arithmetic analogue of the fact that every principal divisor on
  a proper algebraic curve has degree zero.
]

#remark(title: "The Adelic Volume Viewpoint")[
  Multiplication by $x in K^times$ acts on every additive local group $K_v$.
  Its local change-of-volume factor is $norm(x)_v$, so its change-of-volume
  factor on the restricted product of all the $K_v$ is

  $ product_v norm(x)_v $

  The product formula says that a global scalar $x$ preserves total adelic
  volume. Locally it may expand at some places and contract at others, but
  globally the two effects cancel exactly.
]

=== The Intrinsic Definition

#definition(title: "Global Field")[
  A #emph[global field] is a field $K$ with $M_K!=emptyset$ such that:

  + for every place $v in M_K$, the completion $K_v$ is a local field;
  + for every $x in K^times$, the set

    $ {v in M_K : norm(x)_v!=1} $

    is finite;
  + the normalized local moduli satisfy the product formula

    $ product_(v in M_K) norm(x)_v=1 quad "for every " x in K^times $

  Equivalently, after choosing an absolute value $abs(dot)_v$ representing
  each place, there are weights $m_v>0$ such that

  $ product_(v in M_K) abs(x)_v^m_v=1 $

  with only finitely many nonunit factors for each $x in K^times$.
]

#theorem(title: [Artin--Whaples Characterization])[
  A field is a global field in the product-formula sense if and only if it is
  one of the following:

  + a finite extension of $QQ$;
  + a finite extension of $FF_q (t)$ for some prime power $q$.
]

#remark(title: "Why Both Conditions Are Needed")[
  Local compactness says that every individual magnified view of $K$ is
  analytically manageable. The product formula says that these views come from
  one coherent global object. Neither idea alone expresses globality:
  #emph[local fields provide the pieces, and the product formula is the gluing
  law].
]

#quote[
  A global field is not merely a field with many absolute values. It is a
  field whose local changes of scale balance globally.
]
