#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Galois Extensions

Galois theory studies a field extension through its symmetries. Separability
ensures that all conjugates are distinct, while normality ensures that they
remain inside the same field. When both conditions hold, the automorphism
group remembers the entire lattice of intermediate fields.

== Definitions and Basic Theory

Throughout this section, $L slash K$ is a finite extension and
$overline(K)$ is a fixed algebraic closure of $K$ containing $L$.

=== Automorphisms and Normality

#definition(title: "Galois Group and Fixed Fields")[
  Let $Fld_K$ be the category whose objects are fields equipped with an
  embedding of $K$, and whose morphisms are field homomorphisms fixing $K$
  pointwise. Regard $L$ as an object of $Fld_K$. The #emph[Galois group] of
  the extension is, by definition, its automorphism group in this category:

  $ "Gal"(L slash K):=Aut_(Fld_K) (L) $

  Concretely,

  $ "Gal"(L slash K)={sigma in Aut(L) | sigma(a)=a " for every " a in K} $

  with group law given by composition. This group is defined for every finite
  extension; the condition that the extension itself be Galois is introduced
  below. If $H subset.eq "Gal"(L slash K)$ is a subgroup, its #emph[fixed
  field] is

  $ L^H:={x in L | sigma(x)=x " for every " sigma in H} $
]

#remark(title: "The Categorical Meaning of a Fixed Field")[
  Regard a group $H$ as the one-object groupoid $B H$. An action of $H$ on
  $L$ by $K$-automorphisms is precisely a functor

  $ rho_H:B H->Fld_K, quad ast mapsto L, quad sigma mapsto sigma $

  The fixed field is the #emph[limit] of this action diagram:

  $ L^H tilde.eq lim_("B" H) rho_H $

  Concretely, this limit is the simultaneous equalizer

  $ L^H=inter.big_(sigma in H) "Eq"(sigma,"id"_L) $

  Its universal property says that a morphism $R->L$ in $Fld_K$ factors
  through $L^H$ exactly when it is invariant under every element of $H$:

  $ Hom_(Fld_K) (R,L^H) tilde.eq {f in Hom_(Fld_K) (R,L) | sigma compose f=f " for every " sigma in H} $
]

#remark(title: "The Galois Connection Before the Galois Theorem")[
  Put $G="Gal"(L slash K)$. Intermediate fields and subgroups form poset
  categories, and the assignments

  $ E mapsto "Gal"(L slash E), quad H mapsto L^H $

  are contravariant. For every intermediate field $E$ and subgroup
  $H subset.eq G$,

  $ H subset.eq "Gal"(L slash E) <=> E subset.eq L^H $

  This adjunction of order-reversing maps is a #emph[Galois connection]. It
  always gives closure relations

  $ E subset.eq L^("Gal"(L slash E)), quad H subset.eq "Gal"(L slash L^H) $

  The fundamental theorem proved below says that, when $L slash K$ is finite
  Galois, both inclusions are equalities. In categorical language, the Galois
  connection becomes an anti-equivalence of the two poset categories.
]

#lemma(title: "Extension of Embeddings")[
  Let $K subset.eq E subset.eq L$, and let
  $tau:E->overline(K)$ be a $K$-embedding. Then $tau$ extends to a
  $K$-embedding

  $ tilde(tau):L->overline(K) $
]

#proof[
  Choose a tower

  $ E=E_0 subset.eq E_1 subset.eq dots subset.eq E_r=L, quad E_i=E_(i-1) (alpha_i) $

  Suppose the embedding has been extended to $E_(i-1)$. Apply it to the
  coefficients of the minimal polynomial of $alpha_i$. The resulting
  polynomial has a root in the algebraically closed field $overline(K)$, and
  choosing such a root extends the embedding to $E_i$. Induction reaches $L$.
]

#definition(title: "Normal and Galois Extensions")[
  The extension $L slash K$ is #emph[normal] if every irreducible polynomial
  $f in K[T]$ having one root in $L$ splits completely over $L$.

  It is #emph[Galois] if it is both normal and separable.
]

#proposition(title: "Equivalent Forms of Normality")[
  The following conditions are equivalent.

  + The extension $L slash K$ is normal.

  + Every $K$-embedding $sigma:L->overline(K)$ satisfies $sigma(L)=L$.

  + The field $L$ is the splitting field over $K$ of a family of polynomials
    in $K[T]$; since $L slash K$ is finite, the family may be replaced by one
    polynomial.
]

#proof[
  Suppose $L slash K$ is normal. For $alpha in L$, every conjugate of $alpha$
  over $K$ lies in $L$, so every $K$-embedding sends $L$ into $L$. Its image
  has the same degree over $K$ as $L$, hence it equals $L$.

  Conversely, let $alpha in L$ and let $beta in overline(K)$ be any root of
  the minimal polynomial of $alpha$. The embedding
  $K(alpha)->overline(K)$ sending $alpha$ to $beta$ extends to $L$. By the
  second condition its image is $L$, so $beta in L$. Thus every minimal
  polynomial with a root in $L$ splits in $L$.

  If $L slash K$ is finite and normal, choose generators of $L$ and take the
  product of their minimal polynomials. Its splitting field is $L$.
  Conversely, a $K$-embedding permutes the roots of any polynomial over $K$,
  so it preserves its splitting field. This proves the last equivalence.
]

=== Artin's Theorem and Galois Characterizations

#lemma(title: "Artin Independence of Embeddings")[
  Distinct field homomorphisms $sigma_1,dots,sigma_r:L->Omega$ are linearly
  independent over $Omega$ as functions from $L$ to $Omega$.
]

#proof[
  Suppose there is a nontrivial relation of minimal length

  $ a_1 sigma_1+dots+a_r sigma_r=0 $

  and scale it so that $a_1=1$. Choose $x in L$ with
  $sigma_1 (x)!=sigma_r (x)$. Evaluate the relation at $x y$ and subtract
  $sigma_1 (x)$ times the relation evaluated at $y$. This gives a shorter
  nontrivial relation among $sigma_2,dots,sigma_r$, a contradiction.
]

#theorem(title: "Artin's Fixed-Field Theorem")[
  Let $H$ be a finite subgroup of $Aut(L)$ and put $F=L^H$. Then

  $ [L:F]=abs(H), quad "Gal"(L slash F)=H $
]

#proof[
  Write $H={sigma_1,dots,sigma_r}$. Given $r+1$ elements
  $x_1,dots,x_(r+1) in L$, the homogeneous system

  $ sum_(j=1)^(r+1) a_j sigma_i (x_j)=0, quad 1<=i<=r $

  has a nonzero solution $(a_j)$ in $L^(r+1)$. Choose one with minimal support
  and normalize a nonzero coordinate to $1$. For every $tau in H$, applying
  $tau$ to the equation indexed by $tau^(-1) compose sigma_i$ shows that
  $(tau(a_j))$ is another solution. Subtracting the two solutions would reduce
  the support unless $tau(a_j)=a_j$ for every $j$. Hence all $a_j$ lie in $F$,
  and the equation for the identity automorphism gives an $F$-linear relation
  among the $x_j$. Therefore $[L:F]<=r$.

  The preceding lemma says that the $r$ automorphisms in $H$ are linearly
  independent over $L$. Once $[L:F]$ is finite, the $L$-vector space of
  $F$-linear maps $L->L$ has dimension $[L:F]$, so $r<=[L:F]$. Equality
  follows. Finally, $H subset.eq "Gal"(L slash F)$ and every finite extension
  has at most its degree many automorphisms, so $"Gal"(L slash F)=H$.
]

#theorem(title: "Characterizations of a Finite Galois Extension")[
  Put $G="Gal"(L slash K)$ and $n=[L:K]$. The following conditions are
  equivalent.

  + The extension $L slash K$ is Galois.

  + The field $L$ is the splitting field over $K$ of a separable polynomial.

  + The extension has the maximal possible number of automorphisms:

    $ abs(G)=n $

  + The base field is exactly the fixed field:

    $ K=L^G $
]

#proof[
  By Chapter 2, separability gives exactly $n$ embeddings
  $L->overline(K)$. Normality says that all of them have image $L$, so they
  are precisely the elements of $G$ and $abs(G)=n$. Conversely, if
  $abs(G)=n$, then these automorphisms exhaust all possible embeddings. Hence
  there are $n$ distinct embeddings and all have image $L$, which gives
  separability and normality.

  The equivalence with being the splitting field of a separable polynomial
  follows from the normality criterion. Finally, Artin's theorem gives

  $ [L:L^G]=abs(G) $

  Since $K subset.eq L^G$, this equality shows that $abs(G)=n$ exactly when
  $K=L^G$.
]

#quote[
  #emph[Core idea.] A finite extension is Galois precisely when every
  $K$-embedding of $L$ into an algebraic closure is already a symmetry of
  $L$ itself.
]

=== Conjugates and the Galois Action

#proposition(title: "Orbits Are Conjugates")[
  Suppose $L slash K$ is Galois with group $G$, and let $alpha in L$. Define
  its stabilizer

  $ G_alpha:={sigma in G | sigma(alpha)=alpha} $

  Then the roots of the minimal polynomial $m_(alpha,K)$ are exactly the
  distinct elements in the orbit $G dot alpha$. In particular,

  $ deg(m_(alpha,K))=abs(G dot alpha)=[G:G_alpha] $

  and, choosing one representative from every coset,

  $ m_(alpha,K) (T)=product_(sigma in G slash G_alpha) (T-sigma(alpha)) $

  Moreover,

  $ K(alpha)=L^(G_alpha) $
]

#proof[
  Every $sigma(alpha)$ is a root of $m_(alpha,K)$. Conversely, an embedding
  $K(alpha)->overline(K)$ sending $alpha$ to any conjugate extends to an
  embedding of $L$. Since $L slash K$ is normal, the extension belongs to $G$.
  Thus conjugates and orbit elements coincide. The orbit--stabilizer theorem
  gives the degree formula. Finally, $K(alpha) subset.eq L^(G_alpha)$, and
  Artin's theorem together with the degree formula shows that both fields have
  the same degree over $K$.
]

#corollary(title: "Trace and Norm in a Galois Extension")[
  If $L slash K$ is Galois with group $G$, then for every $alpha in L$,

  $ "Tr"_(L slash K) (alpha)=sum_(sigma in G) sigma(alpha), quad "N"_(L slash K) (alpha)=product_(sigma in G) sigma(alpha) $

  Thus trace and norm are respectively the additive and multiplicative
  symmetrizations of an element under the Galois action.
]

=== The Fundamental Correspondence

#theorem(title: "Fundamental Theorem of Galois Theory")[
  Let $L slash K$ be finite Galois with group $G$. The assignments

  $ E mapsto "Gal"(L slash E), quad H mapsto L^H $

  give mutually inverse, inclusion-reversing bijections between intermediate
  fields $K subset.eq E subset.eq L$ and subgroups $H subset.eq G$. If
  $E=L^H$, then

  $ [L:E]=abs(H), quad [E:K]=[G:H] $

  Furthermore, $E slash K$ is Galois if and only if $H$ is normal in $G$. In
  that case restriction induces an isomorphism

  $ "Gal"(E slash K) tilde.eq G slash H $
]

#proof[
  For a subgroup $H$, Artin's theorem gives
  $"Gal"(L slash L^H)=H$. For an intermediate field $E$, the extension
  $L slash E$ is separable, and every $E$-embedding of $L$ is a $K$-embedding
  and hence preserves $L$. Thus $L slash E$ is Galois, and the fixed field of
  $"Gal"(L slash E)$ is $E$. This proves that the assignments are inverse.
  Their order reversal and the degree formulas follow immediately.

  If $H$ is normal, then

  $ sigma(L^H)=L^(sigma H sigma^(-1))=L^H $

  for every $sigma in G$. Hence restriction gives a homomorphism
  $G->"Gal"(E slash K)$ with kernel $H$; the degree formula shows that it is
  surjective. Conversely, if $E slash K$ is normal, every element of $G$
  preserves $E$, so $H$ is the kernel of the restriction map and is therefore
  normal.
]

#block(breakable: false)[
  The correspondence is summarized by the following dictionary.

  #align(center, table(
    columns: (1fr, 1fr),
    align: (center, center),
    inset: (x: 12pt, y: 5.5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[Subgroup side]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Field side]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    [$H subset.eq G$], [$E=L^H$],
    [$H_1 subset.eq H_2$], [$L^(H_2) subset.eq L^(H_1)$],
    [$abs(H)$], [$[L:E]$],
    [$[G:H]$], [$[E:K]$],
    [$H " normal in " G$], [$E slash K " Galois"$],
    [$G slash H$], [$"Gal"(E slash K)$],
  ))
]

=== The Geometric Characterization

#theorem(title: "Tensor-Splitting Characterization")[
  Let $G="Gal"(L slash K)$. The extension $L slash K$ is Galois if and only if
  the
  canonical $L$-algebra map

  $ Psi:L ⊗_K L->product_(sigma in G) L, quad x ⊗ y mapsto (x sigma(y))_(sigma in G) $

  is an isomorphism.
]

#proof[
  Suppose $L slash K$ is Galois and choose a primitive element $theta$. Its
  minimal polynomial has the distinct roots $sigma(theta)$ for $sigma in G$.
  Therefore

  $ L ⊗_K L tilde.eq L[T] slash (m_(theta,K)) tilde.eq product_(sigma in G) L[T] slash (T-sigma(theta)) tilde.eq product_(sigma in G) L $

  by the Chinese remainder theorem, and this is precisely $Psi$. Conversely,
  if $Psi$ is an isomorphism, comparison of dimensions over $L$ gives
  $[L:K]=abs(G)$, so the characterization theorem shows that $L slash K$ is
  Galois.
]

#remark(title: "The Galois Torsor Picture")[
  Passing to spectra reverses the tensor-splitting isomorphism:

  $ "Spec" L times_("Spec" K) "Spec" L tilde.eq ⊔_(sigma in G) "Spec" L $

  The component indexed by $sigma$ is the graph of that automorphism. Thus
  $"Spec" L->"Spec" K$ is a torsor under the finite constant group $G$ in the
  étale topology: after pulling the cover back along itself, it becomes a
  disjoint union of copies of the base. Algebraically, the Galois group is the
  full deck-transformation group of this finite étale cover.
]

=== Basic Examples

#example(title: "Quadratic Extensions")[
  Let $d in QQ^times$ be nonsquare and put $L=QQ(sqrt(d))$. The polynomial
  $T^2-d$ is separable and splits in $L$, so $L slash QQ$ is Galois with

  $ "Gal"(L slash QQ)={"id",c}, quad c(sqrt(d))=-sqrt(d) $

  Thus its Galois group is cyclic of order $2$.
]

#example(title: "A Separable Extension That Is Not Normal")[
  Let $alpha=root(3,2)$ and $L=QQ(alpha)$. The extension has degree $3$ and is
  separable, but the other roots $zeta_3 alpha$ and $zeta_3^2 alpha$ of
  $T^3-2$ do not lie in the real field $L$. Hence $L slash QQ$ is not normal
  and

  $ "Gal"(L slash QQ)={"id"} $

  Its normal closure is $M=QQ(alpha,zeta_3)$, and
  $"Gal"(M slash QQ) tilde.eq S_3$.
]

#example(title: "Finite Fields")[
  For every prime power $q$ and $n>=1$, the extension
  $FF_(q^n) slash FF_q$ is Galois. Its Galois group is cyclic of order $n$,
  generated by the Frobenius automorphism

  $ "Frob"_q:x mapsto x^q $

  The fixed elements of Frobenius are precisely the roots of $T^q-T$, namely
  $FF_q$.
]

#example(title: "Cyclotomic Extensions")[
  Let $m>=2$ and let $zeta_m$ be a primitive $m$th root of unity. The
  cyclotomic field $QQ(zeta_m)$ is the splitting field of the separable
  polynomial $T^m-1$, so it is Galois over $QQ$. Every automorphism is
  determined by

  $ sigma_a (zeta_m)=zeta_m^a, quad a in (ZZ slash m ZZ)^times $

  and this gives a canonical isomorphism

  $ "Gal"(QQ(zeta_m) slash QQ) tilde.eq (ZZ slash m ZZ)^times $
]

== Splitting Primes in Galois Extensions

#remark(title: [$A$--$K$--$L$--$B$--$G$ Convention])[
  From now on, whenever we study primes in a Galois extension, we use the
  following #emph[standing convention] unless explicitly stated otherwise:

  + $A$ is a Dedekind domain;

  + $K:="Frac"(A)$ is its fraction field;

  + $L slash K$ is a finite Galois extension;

  + $B$ is the integral closure of $A$ in $L$;

  + $G:="Gal"(L slash K)$ is the Galois group.

  We further abbreviate

  $ n:=[L:K]=abs(G), quad pi:"Spec" B->"Spec" A $

  Thus the letters $A,K,L,B,G$ will always occur in this order: base ring,
  base field, extension field, integral closure, and symmetry group. Later
  sections may simply say “retain the $A$--$K$--$L$--$B$--$G$ convention.”
]

Under this convention, for a nonzero prime $frak(p)$ of $A$, Chapter 3 gives

$ frak(p)B=product_(frak(q)|frak(p)) frak(q)^(e_(frak(q) slash frak(p))) $

with residue degrees
$f_(frak(q) slash frak(p))=[kappa(frak(q)):kappa(frak(p))]$. The Galois
hypothesis forces all primes above $frak(p)$ to look alike.

=== The Galois Action on Ideals and Primes

#proposition(title: "The Galois Action on Ideals")[
  For $sigma in G$ and a fractional ideal $I$ of $B$, define

  $ sigma(I):={sigma(x) | x in I} $

  Then $sigma(I)$ is a fractional ideal of $B$, and

  $ sigma(I J)=sigma(I) sigma(J), quad (sigma tau) (I)=sigma(tau(I)) $

  Thus the fractional ideal group $"FracId"(B)$ is a multiplicative
  $G$-module. The action preserves prime ideals and restricts to an action on
  $"Spec" B$ over $"Spec" A$.
]

#proof[
  If $b in B$, then $b$ satisfies a monic polynomial $f in A[T]$. Since every
  $sigma in G$ fixes $A$,

  $ f(sigma(b))=sigma(f(b))=0 $

  so $sigma(b)$ is integral over $A$ and lies in $B$. Applying the same
  argument to $sigma^(-1)$ gives $sigma(B)=B$. It follows that the image of a
  finitely generated fractional $B$-ideal is again such an ideal.

  Additivity and multiplicativity of $sigma$ give
  $sigma(I J)=sigma(I)sigma(J)$, and the composition law is immediate. A ring
  automorphism sends prime ideals to prime ideals. Finally, if
  $frak(q) inter A=frak(p)$, then

  $ sigma(frak(q)) inter A=frak(p) $

  because $sigma$ fixes every element of $A$. Hence the action preserves each
  fiber over $"Spec" A$.
]

#remark(title: "Divisors, Ideal Classes, and Geometry")[
  The action on fractional ideals becomes an action on divisors by

  $ sigma(sum_frak(q) n_frak(q)[frak(q)])=sum_frak(q) n_frak(q)[sigma(frak(q))] $

  Principal ideals are preserved because
  $sigma(x B)=sigma(x) B$, so $G$ also acts on the class group $"Cl"(B)$, or
  equivalently on $"Pic"("Spec" B)$.

  Geometrically, each $sigma$ is an automorphism over $"Spec" A$ of the finite
  map below---the algebro-geometric analogue of a deck transformation:

  $ pi:"Spec" B->"Spec" A $

  The next theorem says that $G$ acts transitively on every closed fiber.
]

#theorem(title: [Transitivity on Primes Above $frak(p)$])[
  For every nonzero prime $frak(p)$ of $A$, the action of $G$ on

  $ {frak(q) subset.eq B | frak(q) inter A=frak(p)} $

  is transitive. Equivalently, the $G$-orbits of the nonzero primes of $B$ are
  precisely the fibers of the contraction map

  $ "Spec" B->"Spec" A $
]

#proof[
  Suppose two primes $frak(q)_1,frak(q)_2$ above $frak(p)$ lie in distinct
  $G$-orbits. The primes in the orbit of $frak(q)_1$ are distinct maximal
  ideals and none equals $frak(q)_2$. By the Chinese remainder theorem, choose
  $b in B$ such that

  $ b equiv 0 mod frak(q)_2 $

  and

  $ b equiv 1 mod sigma^(-1) (frak(q)_1) " for every " sigma in G $

  The Galois norm is

  $ "N"_(L slash K) (b)=product_(sigma in G) sigma(b) $

  It belongs to $A$: it lies in $K$ and is integral over $A$. Since the product
  contains the factor $b in frak(q)_2$,

  $ "N"_(L slash K) (b) in frak(q)_2 inter A=frak(p) $

  On the other hand, applying $sigma$ to the chosen congruences gives
  $sigma(b) equiv 1 mod frak(q)_1$ for every $sigma$, and hence

  $ "N"_(L slash K) (b) equiv 1 mod frak(q)_1 $

  This contradicts $frak(p) subset.eq frak(q)_1$, proving transitivity.
]

#remark(title: "The Quotient Picture")[
  Since $L^G=K$ and $A$ is integrally closed,

  $ B^G=B inter K=A $

  Thus $"Spec" A="Spec"(B^G)$ is the affine quotient of $"Spec" B$ by $G$.
  The transitivity theorem is its pointwise shadow: each closed point below is
  one orbit of closed points above. The scheme-theoretic fiber contains more
  information than the orbit alone, because it also remembers ramification
  thickness and residue-field degrees.
]

=== Uniform Ramification and Residue Degrees

#proposition(title: "Conjugate Primes Have the Same Local Data")[
  Let $frak(q)|frak(p)$ and $sigma in G$. The map $sigma$ induces a
  $kappa(frak(p))$-isomorphism

  $ overline(sigma)_(frak(q)):kappa(frak(q))->kappa(sigma(frak(q))), quad x+frak(q) mapsto sigma(x)+sigma(frak(q)) $

  Moreover,

  $ e_(sigma(frak(q)) slash frak(p))=e_(frak(q) slash frak(p)), quad f_(sigma(frak(q)) slash frak(p))=f_(frak(q) slash frak(p)) $

  In particular, separability of the residue extension is also independent of
  the chosen prime above $frak(p)$.
]

#proof[
  The residue-field map is well defined because $sigma(frak(q))$ is the image
  of $frak(q)$, and it fixes $kappa(frak(p))$ because $sigma$ fixes $A$. It is
  an isomorphism with inverse induced by $sigma^(-1)$, proving equality of the
  residue degrees and invariance of separability.

  Since $sigma(frak(p)B)=frak(p)B$, applying $sigma$ to the unique
  prime-ideal factorization of $frak(p)B$ simply permutes its prime factors
  without changing their exponents. This proves equality of the ramification
  indices.
]

#definition(title: "The Galois Splitting Type")[
  By transitivity, the ramification index and residue degree are constant over
  $frak(p)$. We may therefore write

  $ e_(frak(p)):=e_(frak(q) slash frak(p)), quad f_(frak(p)):=f_(frak(q) slash frak(p)), quad g_(frak(p)):=abs({frak(q)|frak(p)}) $

  The triple

  $ (e_(frak(p)),f_(frak(p)),g_(frak(p))) $

  is the #emph[splitting type] of $frak(p)$ in $L$.
]

#corollary(title: "The Galois Fundamental Identity")[
  For every nonzero prime $frak(p)$ of $A$,

  $ e_(frak(p)) f_(frak(p)) g_(frak(p))=[L:K] $

  and the ideal factorization takes the uniform form

  $ frak(p)B=(product_(frak(q)|frak(p)) frak(q))^(e_(frak(p))) $
]

#proof[
  Substitute the common values $e_(frak(p))$ and $f_(frak(p))$ into the
  fundamental identity from Chapter 3:

  $ [L:K]=sum_(frak(q)|frak(p)) e_(frak(q) slash frak(p)) f_(frak(q) slash frak(p)) $

  There are $g_(frak(p))$ equal summands. The uniform factorization follows in
  the same way.
]

#remark(title: "The Fiber and Divisor Pictures")[
  The Chinese remainder theorem gives

  $ "Spec"(B slash frak(p)B) tilde.eq ⊔_(frak(q)|frak(p)) "Spec"(B slash frak(q)^(e_(frak(p)))) $

  The group $G$ permutes these components transitively. Every component has
  the same thickness $e_(frak(p))$ and the same residue degree
  $f_(frak(p))$. In divisor language,

  $ pi^* [frak(p)]=e_(frak(p)) sum_(frak(q)|frak(p)) [frak(q)], quad pi_* [frak(q)]=f_(frak(p))[frak(p)] $

  Thus the identity $e_(frak(p))f_(frak(p))g_(frak(p))=n$ says that the total
  degree of the fiber is obtained by multiplying its common thickness, the
  degree of each point, and the number of points.
]

=== Extreme Splitting Behaviors

The terminology of Chapter 3 becomes particularly simple in a Galois
extension. For the word #emph[inert], we retain the condition that the residue
extension be separable.

#block(breakable: false)[
  #align(center, table(
    columns: (1.05fr, 1.05fr, 2fr),
    align: (center, center, center),
    inset: (x: 9pt, y: 5pt),
    stroke: none,
    table.header(
      table.cell(align: center)[#text(fill: c-thm)[#emph[Behavior]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Splitting type]]],
      table.cell(align: center)[#text(fill: c-thm)[#emph[Fiber picture]]],
    ),
    table.hline(stroke: 0.75pt + c-thm),
    table.vline(x: 1, stroke: 0.75pt + c-thm),
    table.vline(x: 2, stroke: 0.75pt + c-thm),
    [split completely], [$(1,1,n)$], [$n$ distinct $kappa(frak(p))$-rational points],
    [inert], [$(1,n,1)$], [one reduced point of residue degree $n$],
    [totally ramified], [$(n,1,1)$], [one rational point of thickness $n$],
    [general], [$(e,f,g)$, $e f g=n$], [$g$ conjugate points, each of degree $f$ and thickness $e$],
  ))
]

#remark(title: "Perfect Residue Fields")[
  If $kappa(frak(p))$ is perfect, every finite residue extension is separable.
  Then $frak(p)$ is unramified exactly when $e_(frak(p))=1$, and all three named
  behaviors in the table are characterized solely by the displayed triples.
  This applies in particular to rings of integers of number fields, whose
  residue fields are finite.
]

#corollary(title: "Prime-Degree Trichotomy")[
  Suppose $[L:K]=ell$ is prime. The identity

  $ e_(frak(p)) f_(frak(p)) g_(frak(p))=ell $

  leaves exactly three possible splitting types:

  $ (ell,1,1), quad (1,ell,1), quad (1,1,ell) $

  If $kappa(frak(p))$ is perfect, these are respectively the cases in which
  $frak(p)$ is totally ramified, inert, and completely split.
]

#example(title: "Splitting in the Gaussian Extension")[
  Let $L=QQ(i)$, $K=QQ$, $A=ZZ$, and $B=ZZ[i]$. This is a quadratic Galois
  extension, so every rational prime has one of the three splitting types
  above. Dedekind--Kummer applied to $T^2+1$ gives

  + $2$ is totally ramified, with type $(2,1,1)$;

  + if $p equiv 1 mod 4$, then $p$ splits completely, with type $(1,1,2)$;

  + if $p equiv 3 mod 4$, then $p$ is inert, with type $(1,2,1)$.

  Complex conjugation interchanges the two primes above every split prime,
  making the transitive Galois action visible.
]

#remark(title: "Why the Galois Hypothesis Matters")[
  Without normality, the embeddings of $L$ need not preserve $L$, so there may
  be too few automorphisms to move one prime above $frak(p)$ to another. The
  primes above a fixed base prime can then have different ramification indices
  and residue degrees. The uniform triple $(e_(frak(p)),f_(frak(p)),g_(frak(p)))$
  is a genuinely Galois phenomenon.
]

== Decomposition and Inertia Groups

Retain the $A$--$K$--$L$--$B$--$G$ convention, fix a nonzero prime
$frak(p)$ of $A$, and choose one prime $frak(q)|frak(p)$ of $B$. The full
Galois group moves $frak(q)$ through the entire fiber. To understand the
arithmetic near this particular point, we first keep only the automorphisms
that preserve it, and then ask how much of their action remains visible on
its residue field.

#quote[
  The decomposition group remembers the symmetries that preserve the chosen
  branch $frak(q)$; the inertia group remembers the symmetries of that branch
  that become invisible on its reduced closed point.
]

=== The Decomposition Group: Fixing a Branch

#definition(title: "Decomposition Group")[
  The #emph[decomposition group] of $frak(q)$ in $L slash K$ is the stabilizer
  of $frak(q)$ under the Galois action:

  $ D_(frak(q))=D_(frak(q)) (L slash K):="Stab"_G (frak(q))={sigma in G | sigma(frak(q))=frak(q)} $
]

The choice of $frak(q)$ is essential. There is generally no preferred point
above $frak(p)$, but all choices give conjugate subgroups.

#proposition(title: "Conjugacy and the Order of the Decomposition Group")[
  If $tau in G$, then

  $ D_(tau(frak(q)))=tau D_(frak(q)) tau^(-1) $

  Moreover,

  $ [G:D_(frak(q))]=g_(frak(p)), quad abs(D_(frak(q)))=e_(frak(p)) f_(frak(p)) $
]

#proof[
  An element $sigma in G$ stabilizes $tau(frak(q))$ exactly when

  $ tau^(-1) sigma tau(frak(q))=frak(q) $

  This is equivalent to $tau^(-1) sigma tau in D_(frak(q))$, proving the
  conjugacy formula.

  The orbit map induces a map

  $ G slash D_(frak(q)) -> {frak(r) subset.eq B | frak(r) inter A=frak(p)}, quad sigma D_(frak(q)) mapsto sigma(frak(q)) $

  It is well defined because two elements of the same left coset have the
  same effect on $frak(q)$. Conversely, if
  $sigma(frak(q))=tau(frak(q))$, then
  $tau^(-1) sigma in D_(frak(q))$, so the two elements determine the same
  coset. The map is therefore injective, and it is surjective by the
  transitivity theorem. Hence

  $ [G:D_(frak(q))]=abs({frak(r)|frak(p)})=g_(frak(p)) $

  Finally, the Galois fundamental identity gives

  $ abs(D_(frak(q)))=abs(G) slash g_(frak(p))=e_(frak(p)) f_(frak(p)) $
]

#proposition(title: "Global, Local, and Geometric Characterizations")[
  Restriction to the local ring induces an isomorphism

  $ D_(frak(q)) tilde.eq Aut_(Alg_(A_(frak(p)))) (B_(frak(q))) $

  Thus $D_(frak(q))$ can equivalently be viewed as

  + the stabilizer of $frak(q)$ in $G$;

  + the automorphism group of the local extension
    $A_(frak(p)) subset.eq B_(frak(q))$;

  + the automorphism group of the pointed cover
    $("Spec" B,frak(q))->("Spec" A,frak(p))$.
]

#proof[
  If $sigma in D_(frak(q))$ and $s in B without frak(q)$, then
  $sigma(s) in.not frak(q)$. Hence

  $ b/s mapsto sigma(b)/sigma(s) $

  defines an $A_(frak(p))$-algebra automorphism of $B_(frak(q))$.

  Conversely, an $A_(frak(p))$-algebra automorphism of $B_(frak(q))$ extends
  uniquely to an automorphism of its fraction field $L$. It fixes the fraction
  field $K$ of $A_(frak(p))$, so it belongs to $G$. It also preserves the
  unique maximal ideal $frak(q)B_(frak(q))$. Since

  $ frak(q)B_(frak(q)) inter B=frak(q) $

  the extended automorphism stabilizes $frak(q)$ and therefore lies in
  $D_(frak(q))$. The two constructions are inverse to each other.
]

#remark(title: "Why the Word Decomposition?")[
  The factorization of $frak(p)B$ has $g_(frak(p))$ conjugate branches. Choosing
  $frak(q)$ breaks the global symmetry from $G$ to its stabilizer
  $D_(frak(q))$. The coset space $G slash D_(frak(q))$ parametrizes the
  different branches, while $D_(frak(q))$ contains the arithmetic that remains
  after one branch has been selected. In this sense $D_(frak(q))$ is the local
  symmetry group of the decomposition of $frak(p)$.
]

=== The Residue Action and the Inertia Group

Every $sigma in D_(frak(q))$ preserves $frak(q)$ and therefore descends to an
automorphism of the residue field. This gives a homomorphism

$ rho_(frak(q)):D_(frak(q))->"Gal"(kappa(frak(q)) slash kappa(frak(p))) $

defined by

$ rho_(frak(q)) (sigma)(x+frak(q))=sigma(x)+frak(q) $

It is well defined because $sigma(frak(q))=frak(q)$, and it fixes
$kappa(frak(p))$ because $sigma$ fixes $A$ pointwise.

#definition(title: "Inertia Group")[
  The #emph[inertia group] of $frak(q)$ is the kernel of the residue action:

  $ I_(frak(q))=I_(frak(q)) (L slash K):=ker(rho_(frak(q))) $

  Equivalently,

  $ I_(frak(q))={sigma in D_(frak(q)) | sigma(x) equiv x mod frak(q) " for every " x in B} $
]

Thus $D_(frak(q))$ preserves the point $frak(q)$, whereas $I_(frak(q))$
preserves both the point and every residue class at that point.

#theorem(title: "Lifting Residue-Field Automorphisms")[
  The residue extension $kappa(frak(q)) slash kappa(frak(p))$ is normal, and
  the homomorphism

  $ rho_(frak(q)):D_(frak(q))->"Gal"(kappa(frak(q)) slash kappa(frak(p))) $

  is surjective.
]

#proof[
  Put $k:=kappa(frak(p))$ and $l:=kappa(frak(q))$. We first construct enough
  polynomials over $k$ whose roots already lie in $l$.

  Let $overline(c) in l$. By the Chinese remainder theorem, choose a lift
  $c in B$ such that

  $ c+frak(q)=overline(c) $

  and

  $ c equiv 0 mod sigma^(-1) (frak(q)) " for every " sigma in G without D_(frak(q)) $

  Repeated ideals among the $sigma^(-1) (frak(q))$ impose the same condition,
  and every distinct ideal occurring here is maximal and different from
  $frak(q)$, so the Chinese remainder theorem applies. Define

  $ P_c (T):=product_(sigma in G) (T-sigma(c)) $

  The coefficients of $P_c$ are fixed by $G$, hence lie in $K$. They are also
  integral over $A$, because they are polynomials in the integral elements
  $sigma(c)$. Since $A$ is integrally closed, $P_c in A[T]$.

  Reduce $P_c$ modulo $frak(q)$. If $sigma in G without D_(frak(q))$, our
  congruence gives $sigma(c) in frak(q)$. If $sigma in D_(frak(q))$, its image
  is $rho_(frak(q)) (sigma)(overline(c))$. Therefore, for
  $m:=abs(G without D_(frak(q)))$,

  $ overline(P_c)(T)=T^m product_(sigma in D_(frak(q))) (T-rho_(frak(q)) (sigma)(overline(c))) $

  This polynomial lies in $k[T]$, has $overline(c)$ as a root, and splits in
  $l[T]$. The minimal polynomial of $overline(c)$ over $k$ divides
  $overline(P_c)$, so it also splits in $l[T]$. Since $overline(c)$ was
  arbitrary, $l slash k$ is normal.

  It remains to prove surjectivity. Let $F$ be the largest subfield of $l$
  separable over $k$. The preceding argument shows that every minimal
  polynomial over $k$ of an element of $F$ splits in $l$. Its roots are
  separable over $k$, hence lie in $F$; therefore $F slash k$ is Galois.

  If $F=k$, then $l slash k$ is purely inseparable and has no nonidentity
  $k$-automorphisms, so surjectivity is immediate. Otherwise choose a nonzero
  primitive element $overline(c)$ with $F=k(overline(c))$, and make the same
  CRT choice above. Let $h in k[T]$ be its minimal polynomial. After removing
  the zero factors, all roots of $overline(P_c)(T) slash T^m$ are
  $k$-conjugates of $overline(c)$. This quotient belongs to $k[T]$, so its
  only irreducible factor is $h$; hence

  $ overline(P_c)(T) slash T^m=h(T)^r $

  for some $r>=1$. Every root of $h$ must therefore occur as
  $rho_(frak(q)) (sigma)(overline(c))$ for some $sigma in D_(frak(q))$.
  Since $overline(c)$ generates $F$, restriction gives a surjection

  $ D_(frak(q))->"Gal"(F slash k) $

  Finally, restriction from $"Gal"(l slash k)$ to $"Gal"(F slash k)$ is
  injective: an automorphism fixing $F$ fixes the purely inseparable extension
  $l slash F$ pointwise. Its image contains the restrictions of
  $D_(frak(q))$, which already fill $"Gal"(F slash k)$, so it is an
  isomorphism. Thus $rho_(frak(q))$ is surjective.
]

#corollary(title: "The Fundamental Exact Sequence")[
  There is a short exact sequence

  $ 1 -> I_(frak(q)) -> D_(frak(q)) -> "Gal"(kappa(frak(q)) slash kappa(frak(p))) -> 1 $

  Consequently,

  $ D_(frak(q)) slash I_(frak(q)) tilde.eq "Gal"(kappa(frak(q)) slash kappa(frak(p))) $

  If

  $ f_(frak(p))^"i":=[kappa(frak(q)):kappa(frak(p))]_"i" $

  denotes the inseparable degree of the residue extension, then

  $ abs(I_(frak(q)))=e_(frak(p)) f_(frak(p))^"i" $

  If the residue extension is separable, then in addition

  $ abs("Gal"(kappa(frak(q)) slash kappa(frak(p))))=f_(frak(p)), quad abs(I_(frak(q)))=e_(frak(p)) $
]

#proof[
  Exactness at $I_(frak(q))$ and $D_(frak(q))$ follows from the definition of
  the inertia group, and exactness on the right is the surjectivity theorem.
  The first isomorphism theorem also gives the displayed quotient
  isomorphism. Since the residue extension is normal, the separable-degree
  formula from Chapter 2 gives

  $ abs("Gal"(kappa(frak(q)) slash kappa(frak(p))))=[kappa(frak(q)):kappa(frak(p))]_"s" $

  The order formula for $D_(frak(q))$ now yields

  $ abs(I_(frak(q)))=(e_(frak(p)) f_(frak(p))) slash [kappa(frak(q)):kappa(frak(p))]_"s"=e_(frak(p)) f_(frak(p))^"i" $

  When the residue extension is separable, its inseparable degree is one and
  its separable degree is $f_(frak(p))$, proving the final assertions.
]

#corollary(title: "Conjugacy of Inertia Groups")[
  For every $tau in G$,

  $ I_(tau(frak(q)))=tau I_(frak(q)) tau^(-1) $
]

#proof[
  The corresponding statement for decomposition groups was proved above.
  Conjugation by $tau$ identifies the residue action at $frak(q)$ with the
  residue action at $tau(frak(q))$: after using the isomorphism

  $ kappa(frak(q)) tilde.eq kappa(tau(frak(q))) $

  induced by $tau$, the action of $tau sigma tau^(-1)$ is the conjugate of the
  action of $sigma$. It is the identity on the residue field exactly when
  $sigma$ is, so conjugation carries one kernel onto the other.
]

#remark(title: "The Geometry of Inertia")[
  Localizing the fiber at $frak(q)$ gives the zero-dimensional local scheme

  $ "Spec"(B_(frak(q)) slash frak(p)B_(frak(q)))="Spec"(B_(frak(q)) slash frak(q)^(e_(frak(p))) B_(frak(q))) $

  Its reduced closed subscheme is $"Spec" kappa(frak(q))$. The decomposition
  group acts on the entire thickened local fiber, and its quotient
  $D_(frak(q)) slash I_(frak(q))$ is precisely the part of this action visible
  on the reduced point. The inertia group fixes the reduced point together
  with its residue functions but may still act nontrivially in the transverse,
  nilpotent direction.

  When $kappa(frak(p))$ is perfect, $abs(I_(frak(q)))=e_(frak(p))$. Thus
  inertia measures exactly the ramification thickness: the fiber is reduced
  at $frak(q)$ if and only if $I_(frak(q))$ is trivial. Over an imperfect
  residue field, inertia also contains the inseparable factor
  $f_(frak(p))^"i"$, which geometrically records the extra multiplicity that
  appears after passing to an algebraic closure.
]

=== Decomposition and Inertia Fields

#definition(title: "The Two Fixed Fields")[
  Assume that $kappa(frak(q)) slash kappa(frak(p))$ is separable. The fixed
  fields

  $ L^(D_(frak(q))) quad "and" quad L^(I_(frak(q))) $

  are called the #emph[decomposition field] and #emph[inertia field] attached
  to $frak(q)$, respectively. Since $I_(frak(q)) subset.eq D_(frak(q))$, they
  form a tower

  $ K subset.eq L^(D_(frak(q))) subset.eq L^(I_(frak(q))) subset.eq L $
]

#theorem(title: "The Field Tower Separates the Three Local Invariants")[
  In the preceding tower,

  $ [L:L^(I_(frak(q)))]=e_(frak(p)) $

  $ [L^(I_(frak(q))):L^(D_(frak(q)))]=f_(frak(p)) $

  $ [L^(D_(frak(q))):K]=g_(frak(p)) $

  Moreover, $L^(I_(frak(q))) slash L^(D_(frak(q)))$ is Galois with group

  $ D_(frak(q)) slash I_(frak(q)) tilde.eq "Gal"(kappa(frak(q)) slash kappa(frak(p))) $
]

#proof[
  The fundamental theorem of Galois theory gives

  $ [L:L^(I_(frak(q)))]=abs(I_(frak(q)))=e_(frak(p)) $

  and

  $ [L^(D_(frak(q))):K]=[G:D_(frak(q))]=g_(frak(p)) $

  The inertia group is normal in $D_(frak(q))$ because it is the kernel of
  $rho_(frak(q))$. Applying Galois theory to the Galois extension
  $L slash L^(D_(frak(q)))$, whose Galois group is $D_(frak(q))$, shows that
  $L^(I_(frak(q))) slash L^(D_(frak(q)))$ is Galois with group
  $D_(frak(q)) slash I_(frak(q))$. The fundamental exact sequence identifies
  this quotient with the residue-field Galois group, whose order is
  $f_(frak(p))$. This proves the middle equality and all the assertions.
]

#remark(title: "Reading the Tower from Top to Bottom")[
  Descending from $L$ to the inertia field removes the symmetries responsible
  for ramification, contributing the factor $e_(frak(p))$. Descending from the
  inertia field to the decomposition field removes the visible residue-field
  symmetries, contributing $f_(frak(p))$. The remaining degree down to $K$
  counts the conjugate choices of a prime above $frak(p)$, contributing
  $g_(frak(p))$. The identity

  $ [L:K]=e_(frak(p)) f_(frak(p)) g_(frak(p)) $

  is therefore the degree formula for this field tower.
]

=== Behavior in Intermediate Fields

Let $K subset.eq E subset.eq L$, put $B_E:=B inter E$, and let
$frak(q)_E:=frak(q) inter B_E$. Then $B_E$ is the integral closure of $A$ in
$E$, and $frak(q)|frak(q)_E|frak(p)$.

#proposition(title: "Compatibility with an Intermediate Field")[
  Put $H:="Gal"(L slash E)$. Then

  $ D_(frak(q)) (L slash E)=D_(frak(q)) (L slash K) inter H $

  and

  $ I_(frak(q)) (L slash E)=I_(frak(q)) (L slash K) inter H $
]

#proof[
  An element of $G$ belongs to $D_(frak(q)) (L slash E)$ exactly when it fixes
  $E$ pointwise and stabilizes $frak(q)$. The first condition says that it
  lies in $H$, and the second that it lies in
  $D_(frak(q)) (L slash K)$, proving the first equality.

  On this intersection the residue action is simply the restriction of the
  residue action for $L slash K$. Its kernel consists of the elements acting
  trivially on $kappa(frak(q))$, which proves the second equality.
]

#corollary(title: "Maximality of the Inertia and Decomposition Fields")[
  Continue to assume that $kappa(frak(q)) slash kappa(frak(p))$ is separable.
  For every intermediate field $E$,

  $ e_(frak(q)_E slash frak(p))=1 <=> E subset.eq L^(I_(frak(q))) $

  and

  $ e_(frak(q)_E slash frak(p))=f_(frak(q)_E slash frak(p))=1 <=> E subset.eq L^(D_(frak(q))) $

  Thus the inertia field is the largest intermediate field in which the
  selected branch is unramified, while the decomposition field is the largest
  one in which that branch is both unramified and residue-trivial.
]

#proof[
  Let $H="Gal"(L slash E)$, and abbreviate
  $I:=I_(frak(q)) (L slash K)$ and $D:=D_(frak(q)) (L slash K)$. By the
  compatibility proposition and the order formula applied to $L slash E$,

  $ e_(frak(q) slash frak(q)_E)=abs(I inter H) $

  The multiplicativity of ramification indices gives

  $ e_(frak(q) slash frak(p))=e_(frak(q) slash frak(q)_E) e_(frak(q)_E slash frak(p)) $

  Since $e_(frak(q) slash frak(p))=abs(I)$, the equality
  $e_(frak(q)_E slash frak(p))=1$ holds exactly when
  $abs(I inter H)=abs(I)$, equivalently $I subset.eq H$. By the Galois
  correspondence, this is equivalent to $E subset.eq L^I$.

  Likewise, the order formula for the decomposition group and multiplicativity
  of both local invariants give

  $ e_(frak(q) slash frak(q)_E) f_(frak(q) slash frak(q)_E)=abs(D inter H) $

  and

  $ e_(frak(q) slash frak(p)) f_(frak(q) slash frak(p))=e_(frak(q) slash frak(q)_E) f_(frak(q) slash frak(q)_E) e_(frak(q)_E slash frak(p)) f_(frak(q)_E slash frak(p)) $

  The product on the left is $abs(D)$. Hence
  $e_(frak(q)_E slash frak(p))f_(frak(q)_E slash frak(p))=1$ exactly when
  $D subset.eq H$, equivalently $E subset.eq L^D$. Since both invariants are
  positive integers, their product is one exactly when each is one.
]

#example(title: "The Three Gaussian Behaviors Revisited")[
  Let $L=QQ(i)$ and $G={1,"conj"}$ as above.

  + If $p equiv 1 mod 4$, then $p$ splits completely. For either prime
    $frak(q)|p$, the nontrivial element exchanges the two branches, so
    $D_(frak(q))=I_(frak(q))={1}$.

  + If $p equiv 3 mod 4$, then $p$ is inert. There is only one branch, so
    $D_(frak(q))=G$, but the fiber is unramified and
    $I_(frak(q))={1}$. Thus $D_(frak(q))$ acts faithfully on
    $kappa(frak(q)) tilde.eq FF_(p^2)$ over $FF_p$.

  + The prime $2$ is totally ramified. Again there is only one branch, so
    $D_(frak(q))=G$, but now the residue field does not grow. The residue
    action is trivial and $I_(frak(q))=G$; all the nontrivial local symmetry
    lies in the ramification thickness.

  These cases isolate the three numbers in $(e,f,g)$: splitting is detected
  by the index of $D_(frak(q))$, residue-field growth by
  $D_(frak(q)) slash I_(frak(q))$, and ramification by $I_(frak(q))$.
]

== Frobenius Elements and Artin Symbols

Continue with the $A$--$K$--$L$--$B$--$G$ convention and assume that the
residue fields under consideration are finite. For a nonzero prime
$frak(p)$ of $A$, write

$ "N"(frak(p)):=abs(kappa(frak(p))) $

This agrees with the absolute ideal norm in the number-field case. If
$frak(q)|frak(p)$, then $kappa(frak(q))$ is also finite. The finite-field
Frobenius gives a distinguished automorphism of this residue extension. At
an unramified prime, the fundamental exact sequence lets us lift that
automorphism uniquely to $G$.

#quote[
  A Frobenius element is the global Galois symmetry whose reduction at one
  chosen prime is the canonical Frobenius symmetry of the finite residue
  field. Its conjugacy class records the prime without remembering the choice
  of a point above it.
]

=== Frobenius on the Residue Field

#proposition(title: "Finite-Field Frobenius")[
  Let $frak(q)|frak(p)$ and put $f=f_(frak(p))$. The residue extension is
  Galois and cyclic:

  $ "Gal"(kappa(frak(q)) slash kappa(frak(p)))=lr(⟨ phi_(frak(q) slash frak(p)) ⟩) $

  where

  $ phi_(frak(q) slash frak(p)):x mapsto x^("N"(frak(p))) $

  The order of $phi_(frak(q) slash frak(p))$ is $f$.
]

#proof[
  Put $Q="N"(frak(p))$. Then

  $ kappa(frak(p)) tilde.eq FF_Q, quad kappa(frak(q)) tilde.eq FF_(Q^f) $

  The map $x mapsto x^Q$ fixes $FF_Q$ and its $r$th power is
  $x mapsto x^(Q^r)$. Its fixed field inside $FF_(Q^f)$ is
  $FF_(Q^(gcd(r,f)))$, so its smallest positive power equal to the identity is
  the $f$th. Thus it generates a cyclic subgroup of order $f$. Since the
  extension has degree $f$, this subgroup is the entire Galois group.
]

#remark(title: "Arithmetic versus Geometric Frobenius")[
  We use the #emph[arithmetic Frobenius]

  $ x mapsto x^("N"(frak(p))) $

  throughout. Many texts in algebraic geometry instead call its inverse the
  #emph[geometric Frobenius]. With that convention every Frobenius element and
  Artin symbol below is replaced by its inverse. Neither convention changes
  the resulting conjugacy classes up to applying inversion, but formulas must
  not mix the two choices.
]

=== Frobenius Elements and Frobenius Classes

Suppose now that $frak(p)$ is unramified. Finite residue fields are perfect,
so $I_(frak(q))={1}$ and the fundamental exact sequence becomes an
isomorphism

$ rho_(frak(q)):D_(frak(q)) tilde.eq "Gal"(kappa(frak(q)) slash kappa(frak(p))) $

#definition(title: "Frobenius Element")[
  The #emph[Frobenius element] at $frak(q)$ is the unique inverse image of the
  residue-field Frobenius:

  $ "Frob"_(frak(q)):=rho_(frak(q))^(-1) (phi_(frak(q) slash frak(p))) in D_(frak(q)) subset.eq G $
]

The restriction to unramified primes is essential. At a ramified prime the
map $rho_(frak(q))$ has kernel $I_(frak(q))$, so a residue-field Frobenius has
an entire $I_(frak(q))$-coset of lifts rather than a distinguished lift.

#theorem(title: "Congruence Characterization and Order")[
  The element $"Frob"_(frak(q))$ is the unique $sigma in G$ satisfying

  $ sigma(x) equiv x^("N"(frak(p))) mod frak(q) " for every " x in B $

  Moreover,

  $ D_(frak(q))=lr(⟨ "Frob"_(frak(q)) ⟩), quad "ord"("Frob"_(frak(q)))=f_(frak(p)) $
]

#proof[
  By definition, $"Frob"_(frak(q))$ reduces to
  $x mapsto x^("N"(frak(p)))$, so it satisfies the congruence.

  Conversely, suppose $sigma in G$ satisfies it. For every $x in frak(q)$,
  the right-hand side is zero modulo $frak(q)$, hence
  $sigma(x) in frak(q)$. Thus $sigma(frak(q)) subset.eq frak(q)$. Both are
  maximal ideals of $B$, so equality holds and $sigma in D_(frak(q))$. Its
  image under $rho_(frak(q))$ is the residue-field Frobenius. Since
  $rho_(frak(q))$ is an isomorphism, $sigma="Frob"_(frak(q))$.

  The same isomorphism identifies $D_(frak(q))$ with the cyclic residue-field
  Galois group, whose generator is $phi_(frak(q) slash frak(p))$ and whose
  order is $f_(frak(p))$. Its inverse image therefore generates
  $D_(frak(q))$ and has the stated order.
]

#theorem(title: "Frobenius Elements Form a Conjugacy Class")[
  If $frak(p)$ is unramified, then for every $tau in G$,

  $ "Frob"_(tau(frak(q)))=tau "Frob"_(frak(q)) tau^(-1) $

  Consequently,

  $ {"Frob"_(frak(r)) : frak(r)|frak(p)} $

  is one conjugacy class in $G$.
]

#proof[
  Let $x in B$ and put $y=tau^(-1) (x)$. The congruence characterization at
  $frak(q)$ gives

  $ "Frob"_(frak(q)) (y)-y^("N"(frak(p))) in frak(q) $

  Applying $tau$ and using that a field automorphism commutes with integer
  powers yields

  $ tau "Frob"_(frak(q)) tau^(-1) (x)-x^("N"(frak(p))) in tau(frak(q)) $

  The uniqueness part of the preceding theorem therefore gives the conjugacy
  formula.

  By transitivity, every prime $frak(r)|frak(p)$ has the form
  $tau(frak(q))$, so every Frobenius element above $frak(p)$ is a conjugate of
  $"Frob"_(frak(q))$. Conversely, the formula shows that every conjugate is
  the Frobenius element at a prime above $frak(p)$. The two sets are equal.
]

#definition(title: "Frobenius Class")[
  For an unramified prime $frak(p)$, its #emph[Frobenius class] is

  $ "Frob"_(frak(p)):={"Frob"_(frak(q)) : frak(q)|frak(p)} subset.eq G $

  It is canonical: it depends on $frak(p)$ but not on a choice of
  $frak(q)|frak(p)$. If $G$ is abelian, every conjugacy class is a singleton,
  so all the elements $"Frob"_(frak(q))$ above $frak(p)$ are equal; in this
  case we also denote their common value by $"Frob"_(frak(p))$.
]

#remark(title: "The Geometric Meaning of Frobenius")[
  Because $frak(p)$ is unramified and its residue field is finite, the fiber

  $ X_(frak(p)):="Spec"(B slash frak(p)B) $

  is finite étale over $"Spec" kappa(frak(p))$. Each component is a closed
  point $x_(frak(q))="Spec" kappa(frak(q))$. The decomposition group is the
  symmetry group preserving this component, and $"Frob"_(frak(q))$ is the
  unique symmetry whose action on its residue field is
  $x mapsto x^("N"(frak(p)))$.

  Thus a Frobenius element is a form of #emph[arithmetic monodromy]: it records
  how the canonical finite-field symmetry is lifted through the cover
  $"Spec" B->"Spec" A$. Changing the chosen point conjugates the lift, which
  is why the intrinsic datum attached to $frak(p)$ is a conjugacy class rather
  than an individual group element.
]

=== Artin Symbols and Splitting

#definition(title: [Artin Symbol at a Prime Above $frak(p)$])[
  For an unramified prime $frak(q)|frak(p)$, the #emph[Artin symbol] is another
  notation for its Frobenius element:

  $ lr((frac(L slash K,frak(q)))):="Frob"_(frak(q)) $

  Our Artin symbols therefore use arithmetic Frobenius. Under the geometric
  Frobenius convention, the right-hand side would be inverted.
]

#corollary(title: "The Frobenius Class Determines the Splitting Type")[
  For every unramified $frak(p)$ and every $frak(q)|frak(p)$,

  $ f_(frak(p))="ord"("Frob"_(frak(q))), quad g_(frak(p))=[L:K] slash "ord"("Frob"_(frak(q))) $

  In particular,

  + $frak(p)$ splits completely if and only if
    $lr((frac(L slash K,frak(q))))=1$;

  + $frak(p)$ is inert if and only if $"Frob"_(frak(q))$ generates $G$.
]

#proof[
  The order formula was proved in the congruence-characterization theorem.
  Since $frak(p)$ is unramified, $e_(frak(p))=1$, so

  $ f_(frak(p)) g_(frak(p))=[L:K] $

  gives the formula for $g_(frak(p))$.

  Complete splitting is equivalent to $f_(frak(p))=1$, hence to the
  Frobenius element being the identity. The prime is inert exactly when
  $g_(frak(p))=1$, equivalently $D_(frak(q))=G$. But
  $D_(frak(q))=lr(⟨ "Frob"_(frak(q)) ⟩)$, which proves the second
  criterion.
]

#remark(title: "Why One Conjugacy Class Is Enough")[
  Conjugate elements have the same order. Therefore the Frobenius class alone
  recovers $f_(frak(p))$ and, for an unramified prime, the entire splitting
  type

  $ (e_(frak(p)),f_(frak(p)),g_(frak(p)))=(1,"ord"("Frob"_(frak(p))),[L:K] slash "ord"("Frob"_(frak(p)))) $

  Here the order of a conjugacy class means the common order of any of its
  elements.

  This is the first indication that Frobenius classes encode the arithmetic
  of prime decomposition very efficiently.
]

=== Compatibility in Towers

#proposition(title: "Functoriality of Artin Symbols")[
  Let $K subset.eq E subset.eq L$, put $B_E=B inter E$, and let
  $frak(q)_E=frak(q) inter B_E$. Suppose $frak(q)|frak(p)$ is unramified. Then

  $ lr((frac(L slash E,frak(q))))=lr((frac(L slash K,frak(q))))^(f_(frak(q)_E slash frak(p))) $

  If $E slash K$ is Galois, restriction also gives

  $ lr((frac(E slash K,frak(q)_E)))=lr((frac(L slash K,frak(q))))|_E $
]

#proof[
  Put $sigma=lr((frac(L slash K,frak(q))))$ and
  $d=f_(frak(q)_E slash frak(p))$. Since the total ramification index is one,
  both subextensions are unramified. We have

  $ D_(frak(q)) (L slash E)=D_(frak(q)) (L slash K) inter "Gal"(L slash E) $

  The group on the right is a subgroup of the cyclic group
  $D_(frak(q)) (L slash K)=lr(⟨ sigma ⟩)$. Its index in that cyclic
  group is

  $ f_(frak(q) slash frak(p)) slash f_(frak(q) slash frak(q)_E)=f_(frak(q)_E slash frak(p))=d $

  by multiplicativity of residue degrees. The unique subgroup of index $d$
  in $lr(⟨ sigma ⟩)$ is $lr(⟨ sigma^d ⟩)$. Moreover,

  $ abs(kappa(frak(q)_E))="N"(frak(p))^d $

  so $sigma^d$ acts on $kappa(frak(q))$ by
  $x mapsto x^(abs(kappa(frak(q)_E)))$. The congruence characterization relative to
  $L slash E$ now shows

  $ lr((frac(L slash E,frak(q))))=sigma^d $

  For the second assertion, suppose $E slash K$ is Galois. The restriction
  $sigma|_E$ stabilizes $frak(q)_E$ and induces
  $x mapsto x^("N"(frak(p)))$ on its residue field. By uniqueness, it is the
  Frobenius element of $frak(q)_E$ in $E slash K$.
]

=== The Artin Map in an Abelian Extension

Suppose now that $G$ is abelian. The Frobenius elements above an unramified
prime $frak(p)$ are all equal, so it is meaningful to put

$ lr((frac(L slash K,frak(p)))):="Frob"_(frak(p)) $

without choosing $frak(q)|frak(p)$.

#definition(title: "Artin Map")[
  Let $S$ be the set of primes of $A$ ramified in $L$, and let

  $ "I"_A^S:={I in "FracId"(A) | v_(frak(p)) (I)=0 " for every " frak(p) in S} $

  be the group of fractional ideals prime to $S$. The #emph[Artin map] is

  $ "Art"_(L slash K):"I"_A^S->G $

  determined by

  $ "Art"_(L slash K) (product_(i=1)^r frak(p)_i^(a_i)):=product_(i=1)^r lr((frac(L slash K,frak(p)_i)))^(a_i) $

  where the $frak(p)_i$ are unramified and $a_i in ZZ$.
]

#proposition(title: "Well-Definedness and Multiplicativity")[
  The Artin map is a well-defined group homomorphism. On every unramified
  prime,

  $ "Art"_(L slash K) (frak(p))="Frob"_(frak(p)) $
]

#proof[
  Unique factorization of fractional ideals in the Dedekind domain $A$ writes
  every element of $"I"_A^S$ uniquely as a finite product
  $product frak(p)^(a_(frak(p)))$ over primes outside $S$. The Frobenius class
  at each such prime is a singleton because $G$ is abelian, so every factor
  on the right is unambiguous. The product is independent of its ordering
  because $G$ is abelian. Finally, multiplication of ideals adds their prime
  exponents, while multiplication in $G$ adds the corresponding exponents of
  each Artin symbol. This proves both well-definedness and multiplicativity.
]

#remark(title: "Why Ramified Primes Are Removed")[
  At a ramified prime the exact sequence has nontrivial kernel
  $I_(frak(q))$. The residue Frobenius therefore determines only a coset of
  possible lifts in $D_(frak(q))$, not a canonical group element. Removing
  ramified primes is exactly what makes the Artin map canonical.
]

#remark(title: "Arithmetic Significance")[
  The Artin symbol converts the factorization behavior of primes into group
  elements. The identity detects complete splitting, the order gives the
  residue degree, and in a nonabelian extension the conjugacy class is the
  natural invariant. Chebotarev's density theorem describes how these classes
  are distributed among primes. In the abelian setting, Artin reciprocity
  later shows that the Artin map factors through an appropriate ray class
  group and recovers the Galois group from ideal classes and congruence data.
]

=== Basic Examples

#example(title: "Gaussian Integers")[
  Let $L=QQ(i)$ over $K=QQ$. The only ramified rational prime is $2$. For every
  odd prime $p$,

  $ lr((frac(QQ(i) slash QQ,(p))))=cases(
    "id" & quad p equiv 1 mod 4,
    "conj" & quad p equiv 3 mod 4
  ) $

  Indeed, the first case is complete splitting and the second is inertness.
  If $G$ is identified with ${plus.minus 1}$ by sending complex conjugation to
  $-1$, this Artin symbol is the Legendre symbol
  $lr((frac(-1,p)))$.
]

#example(title: "Cyclotomic Fields")[
  Let $L=QQ(zeta_m)$ and identify

  $ "Gal"(L slash QQ) tilde.eq (ZZ slash m ZZ)^times, quad a mapsto (zeta_m mapsto zeta_m^a) $

  For every rational prime $p$ not dividing $m$, the prime is unramified and

  $ lr((frac(QQ(zeta_m) slash QQ,(p))))(zeta_m)=zeta_m^p $

  Thus the Artin symbol of $p$ corresponds exactly to the residue class of
  $p$ in $(ZZ slash m ZZ)^times$. The order of $p$ modulo $m$ is therefore the
  residue degree of $p$ in the cyclotomic extension.
]
