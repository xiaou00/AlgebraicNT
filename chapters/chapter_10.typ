#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= The Different and the Discriminant

We return to the Dedekind-extension setup used throughout the first part of
the book:

+ $A$ is a Dedekind domain with fraction field $K$;

+ $L slash K$ is a finite separable extension of degree $n$;

+ $B$ is the integral closure of $A$ in $L$.

For brevity we continue to call this the #emph[$A K L B$ setup]. The goal of
this chapter is to construct two ideals that record ramification:

$ "Diff"_(B slash A) subset.eq B, quad "Disc"_(B slash A) subset.eq A $

The #emph[different] lives upstairs on $"Spec" B$; the #emph[discriminant]
lives downstairs on $"Spec" A$. They contain the same information, transported
by the ideal norm:

$ "Disc"_(B slash A)="N"_(B slash A) ("Diff"_(B slash A)) $

#quote[
  #emph[Core idea.] The different measures where the integral trace pairing
  fails to be perfect upstairs. The discriminant pushes this defect down to
  the base and marks the branch locus.
]

== The Different: the Dual of the Integer Ring

=== Trace Duals of Fractional Ideals

The trace pairing

$ L times L -> K, quad (x,y) mapsto "Tr"_(L slash K) (x y) $

is perfect because $L slash K$ is separable. Chapter 3 associated to every
$A$-lattice $M subset.eq L$ its trace-dual lattice

$ M^∗:={x in L | "Tr"_(L slash K) (x M) subset.eq A} $

and proved $M^(∗∗)=M$. Every nonzero fractional $B$-ideal is an $A$-lattice
in $L$, so it makes sense to dualize it.

#lemma(title: "The Dual of a Fractional Ideal Is a Fractional Ideal")[
  Let $I$ be a nonzero fractional ideal of $B$. Then $I^∗$ is again a
  nonzero fractional ideal of $B$.
]

#proof[
  Trace duality already shows that $I^∗$ is a finitely generated
  $A$-module spanning $L$. It remains only to check stability under $B$.
  If $b in B$, $x in I^∗$, and $m in I$, then $b m in I$, hence

  $ "Tr"_(L slash K) ((b x)m)="Tr"_(L slash K) (x(b m)) in A $

  Therefore $b x in I^∗$. Thus $I^∗$ is a finitely generated $B$-submodule
  of $L$ and hence a fractional $B$-ideal.
]

#definition(title: "Codifferent and Different")[
  The #emph[codifferent] of $B slash A$ is the fractional $B$-ideal

  $ B^∗={x in L | "Tr"_(L slash K) (x B) subset.eq A} $

  The #emph[different] is its inverse:

  $ "Diff"_(B slash A):=(B^∗)^(-1)=(B:B^∗) $

  Equivalently,

  $ "Diff"_(B slash A)={x in L | x B^∗ subset.eq B} $

  We also write $"Diff"_(L slash K)$ when the rings $A$ and $B$ are
  understood.
]

#proposition(title: "The Different Is an Integral Ideal")[
  One has

  $ B subset.eq B^∗, quad "Diff"_(B slash A) subset.eq B $

  Thus the different is an integral $B$-ideal, not merely a fractional ideal.
]

#proof[
  If $a,b in B$, then $a b$ is integral over $A$, so
  $"Tr"_(L slash K) (a b) in A$. Hence $a in B^∗$ and $B subset.eq B^∗$.
  Taking inverses reverses inclusion and yields

  $ "Diff"_(B slash A)=(B^∗)^(-1) subset.eq B^(-1)=B $
]

#remark(title: "Why the Inverse Appears")[
  The codifferent is the largest lattice on which pairing with $B$ remains
  integral. If $B^∗=B$, the trace pairing identifies $B$ with its
  $A$-linear dual and there is no defect. When $B^∗$ is larger than $B$, its
  inverse is smaller than $B$; the powers of prime ideals occurring in this
  smaller ideal measure the size of the defect.
]

#remark(title: "Linear-Algebra Analogy")[
  For a Euclidean lattice $Lambda subset.eq RR^n$, the dual lattice consists
  of vectors having integral inner product with every vector of $Lambda$.
  The codifferent is the arithmetic version of $Lambda^∨$. The difference is
  that the answer is organized prime by prime, so its volume defect becomes
  an ideal rather than a positive real number.
]

=== Localization and Completion

The different is local: its exponent at a prime can be computed after
discarding all other primes, or even after completing.

#proposition(title: "Localization of the Different")[
  Let $S subset.eq A$ be multiplicatively closed. Then

  $ S^(-1) "Diff"_(B slash A)="Diff"_(S^(-1)B slash S^(-1)A) $
]

#proof[
  Trace duals commute with localization:

  $ S^(-1)(B^∗)=(S^(-1)B)^∗ $

  Indeed, the inclusion from left to right is immediate. For the reverse
  inclusion, test against a finite set of $A$-generators of $B$ and clear the
  finitely many denominators. Inversion of fractional ideals also commutes
  with localization. Applying both facts gives the formula.
]

#proposition(title: "Completion of the Different")[
  Let $frak(q)|frak(p)$, let $hat(A)_frak(p)$ be the
  $frak(p)$-adic completion of $A_(frak(p))$, and let
  $hat(B)_frak(q)$ be the $frak(q)$-adic completion of $B_(frak(q))$. Then

  $ "Diff"_(hat(B)_frak(q) slash hat(A)_frak(p))
    ="Diff"_(B slash A) hat(B)_frak(q) $
]

#proof[
  Put $K_frak(p):="Frac"(hat(A)_frak(p))$. The decomposition of the completed
  algebra gives

  $ L ⊗_K K_frak(p) tilde.eq product_(frak(q)|frak(p)) L_frak(q) $

  and

  $ B ⊗_A hat(A)_frak(p) tilde.eq product_(frak(q)|frak(p)) hat(B)_frak(q) $

  The trace of a product algebra is the sum of the traces of its factors, so
  the trace pairing is an orthogonal product. Consequently its dual is the
  product of the local duals:

  $ (B ⊗_A hat(A)_frak(p))^∗
    tilde.eq product_(frak(q)|frak(p)) hat(B)_frak(q)^∗ $

  On the other hand, finite projectivity and flat base change give
  $(B ⊗_A hat(A)_frak(p))^∗ tilde.eq
  B^∗ ⊗_A hat(A)_frak(p)$. Taking the component indexed by
  $frak(q)$ and then inverting proves the claim.
]

#remark(title: "A Practical Consequence")[
  To compute $v_frak(q) ("Diff"_(B slash A))$, one may replace the global
  extension by the complete extension $L_frak(q) slash K_frak(p)$. This is
  why the local theory of Eisenstein polynomials from Chapter 9 computes
  global ramification exponents.
]

== The Discriminant

=== Discriminants of Tuples and Polynomials

#definition(title: "Discriminant of a Tuple")[
  Let $S slash R$ be a ring extension for which $S$ is free of rank $n$ as
  an $R$-module. For $x_1,dots,x_n in S$, define

  $ "disc"_(S slash R) (x_1,dots,x_n)
    :=det(("Tr"_(S slash R) (x_i x_j))_(1<=i,j<=n)) in R $

  The elements need not be an $R$-basis. If they satisfy a nontrivial
  $R$-linear relation, their discriminant is zero.
]

#theorem(title: "Embedding Matrix and Vandermonde Formulas")[
  Let $L slash K$ be finite separable of degree $n$, and choose the distinct
  $K$-embeddings

  $ sigma_1,dots,sigma_n:L->Omega $

  into a splitting field $Omega$. For $e_1,dots,e_n in L$,

  $ "disc"(e_1,dots,e_n)=det((sigma_i (e_j))_(i,j))^2 $

  In particular, for every $x in L$,

  $ "disc"(1,x,dots,x^(n-1))
    =product_(1<=i<j<=n) (sigma_i (x)-sigma_j (x))^2 $
]

#proof[
  Set $M=(sigma_i (e_j))_(i,j)$. Since

  $ "Tr"_(L slash K) (e_i e_j)=sum_(r=1)^n sigma_r (e_i)sigma_r (e_j) $

  the Gram matrix of the trace pairing is $M^t M$. Therefore

  $ "disc"(e_1,dots,e_n)=det(M^t M)=det(M)^2 $

  For $e_j=x^(j-1)$, the matrix $M$ is a Vandermonde matrix, whose
  determinant is $product_(i<j)(sigma_j (x)-sigma_i (x))$. Squaring removes
  the choice of order.
]

#definition(title: "Discriminant of a Polynomial")[
  Let

  $ f(X)=product_(i=1)^n (X-alpha_i) $

  be a monic polynomial in a splitting algebra. Its discriminant is

  $ "disc"(f):=product_(i<j) (alpha_i-alpha_j)^2 $

  If $f in A[X]$ is monic and separable and $alpha$ is the image of $X$ in
  $A[X] slash (f)$, then

  $ "disc"(f)="disc"(1,alpha,dots,alpha^(n-1)) in A $
]

#proposition(title: "Derivative and Resultant Formulas")[
  For a monic degree-$n$ polynomial $f$,

  $ "disc"(f)=(-1)^(n(n-1)/2) "Res"(f,f') $

  If $f$ is the minimal polynomial of $alpha$, then

  $ "disc"(f)=(-1)^(n(n-1)/2) "N"_(K(alpha) slash K) (f'(alpha)) $
]

#proof[
  At a root $alpha_i$,

  $ f'(alpha_i)=product_(j!=i)(alpha_i-alpha_j) $

  Multiplying over $i$ counts each unordered pair twice, once in each order,
  and contributes the sign $(-1)^(n(n-1)/2)$. For monic $f$, the resultant
  $"Res"(f,f')$ is $product_i f'(alpha_i)$; the same product is the field
  norm of $f'(alpha)$ when $f$ is irreducible.
]

#example(title: "Low-Degree Formulas")[
  Direct computation gives

  $ "disc"(X^2+b X+c)=b^2-4c $

  and

  $ "disc"(X^3+a X+b)=-4a^3-27b^2 $

  The first formula says that the two roots collide modulo a prime precisely
  when the usual quadratic discriminant vanishes modulo that prime.
]

#remark(title: "What the Vandermonde Product Sees")[
  The discriminant is zero exactly when two geometric points represented by
  the roots collide. Over a residue field this collision may create a
  multiple root or an inseparable factor. Thus the same determinant that
  measures a lattice volume also detects whether a finite fiber is reduced
  and separable.
]

=== The Discriminant Ideal of a Lattice

The ring $B$ need not be free over $A$, so a global basis-dependent number is
not adequate. As with module indices, the correct invariant is an ideal.

#definition(title: "Discriminant Ideal of a Lattice")[
  Let $M subset.eq L$ be an $A$-lattice. Its #emph[discriminant ideal] is the
  $A$-submodule

  $ "Disc"(M):=("disc"(x_1,dots,x_n):x_1,dots,x_n in M) subset.eq K $
]

#lemma(title: "The Free Case")[
  If $M$ is free with basis $e_1,dots,e_n$, then

  $ "Disc"(M)=("disc"(e_1,dots,e_n)) $

  This is a nonzero principal fractional ideal. If $M' subset.eq M$ are free
  lattices and $"Disc"(M')="Disc"(M)$, then $M'=M$.
]

#proof[
  Write $e=(e_1,dots,e_n)$ as a row vector. Every tuple
  $x=(x_1,dots,x_n)$ in $M$ has the form $x=e P$ for some
  $P in "Mat"_n (A)$. Bilinearity of the trace gives

  $ "disc"(x)=det(P^t)"disc"(e)det(P)=det(P)^2 "disc"(e) $

  so all tuple discriminants lie in the ideal generated by $"disc"(e)$, and
  the reverse inclusion is obtained from the basis tuple. Nondegeneracy of
  the trace pairing makes $"disc"(e)$ nonzero.

  If $e'=e P$ is a basis of $M'$, equality of the two principal ideals forces
  $det(P)$ to be a unit. Then $P$ is invertible over $A$ and $M'=M$.
]

#proposition(title: "The Discriminant Ideal Exists")[
  For every $A$-lattice $M subset.eq L$, the module $"Disc"(M)$ is a nonzero
  fractional ideal of $A$.
]

#proof[
  Choose a $K$-basis $e_1,dots,e_n$ contained in $M$ and put
  $N=sum_i A e_i$. Then $"disc"(e_1,dots,e_n)!=0$, so $"Disc"(M)$ is
  nonzero. Since $M$ is finitely generated, there is $0!=a in A$ with
  $M subset.eq a^(-1)N$. Hence

  $ "Disc"(M) subset.eq "Disc"(a^(-1)N)=a^(-2n)"Disc"(N) $

  The right-hand side is a principal fractional ideal and therefore a
  Noetherian $A$-module. Its submodule $"Disc"(M)$ is finitely generated,
  proving the claim.
]

#definition(title: "Discriminant of a Dedekind Extension")[
  In the $A K L B$ setup, define

  $ "Disc"_(B slash A):="Disc"(B) $

  This is an integral $A$-ideal because
  $"Tr"_(L slash K) (x_i x_j) in A$ for all $x_i,x_j in B$.
]

#proposition(title: "Change of Lattice")[
  For arbitrary $A$-lattices $M,N subset.eq L$,

  $ "Disc"(N)=[M:N]_A^2 "Disc"(M) $

  In particular, if $N subset.eq M$, the discriminant gains twice the module
  index divisor.
]

#proof[
  Localize at a nonzero prime $frak(p)$. Both lattices become free over the
  DVR $A_(frak(p))$. If a change-of-basis matrix from $M_(frak(p))$ to
  $N_(frak(p))$ is $P$, then the preceding determinant computation gives

  $ "Disc"(N)_(frak(p))=det(P)^2 "Disc"(M)_(frak(p)) $

  while $[M:N]_A A_(frak(p))=(det P)$. Fractional ideals over a Dedekind
  domain are determined by their localizations, so the global formula follows.
]

#remark(title: "Determinant-Line Interpretation")[
  The trace pairing gives a morphism of vector bundles on $"Spec" A$,

  $ tilde(M)->tilde(M)^∨ $

  Its determinant is a section of $("det" tilde(M)^∨)^(⊗ 2)$. The zero
  divisor of this section is precisely the discriminant divisor. Replacing
  $M$ by a sublattice changes each determinant line once, hence changes the
  discriminant by the #emph[square] of the module index.
]

#example(title: "The Gaussian Field")[
  Take $A=ZZ$, $K=QQ$, $L=QQ(i)$, and $B=ZZ[i]$. With the basis $(1,i)$,

  $ "disc"(1,i)=det mat(2,0;0,-2)=-4 $

  Thus

  $ "Disc"_(ZZ[i] slash ZZ)=(-4)=(4) $

  The same answer follows from the embedding matrix
  $mat(1,1;i,-i)$, whose determinant is $-2i$, or from
  $"disc"(X^2+1)=-4$.
]

#definition(title: "Absolute Discriminant of a Number Field")[
  If $L$ is a number field and $cal(O)_L$ has a $ZZ$-basis
  $e_1,dots,e_n$, its #emph[absolute discriminant] is the integer

  $ d_L:="disc"(e_1,dots,e_n) $

  This integer is independent of the integral basis: a change-of-basis
  determinant is a unit of $ZZ$, hence is $plus.minus 1$, and its square is
  $1$. The discriminant ideal is $(d_L)$.
]

#remark(title: "The Sign of an Absolute Discriminant")[
  If $L$ has signature $(r_1,r_2)$, then

  $ "sign"(d_L)=(-1)^(r_2) $

  Each pair of complex-conjugate embeddings contributes one negative sign to
  the square of the embedding determinant. Thus the ideal remembers the
  ramified primes, while the canonical integer over $ZZ$ also remembers the
  parity of the number of complex places.
]

=== Localization and Products of Local Discriminants

#proposition(title: "Localization of the Discriminant")[
  For every multiplicatively closed subset $S subset.eq A$,

  $ S^(-1) "Disc"_(B slash A)
    ="Disc"_(S^(-1)B slash S^(-1)A) $
]

#proof[
  A generator $s^(-1)"disc"(e_1,dots,e_n)$ of the left-hand side can be
  rewritten as

  $ s^(2n-1) "disc"(s^(-1)e_1,dots,s^(-1)e_n) $

  and therefore lies on the right. Conversely, any finite tuple in
  $S^(-1)B$ has a common denominator $s in S$; multiplying every entry by
  $s$ gives

  $ "disc"(x_1,dots,x_n)
    =s^(-2n)"disc"(s x_1,dots,s x_n) in S^(-1)"Disc"_(B slash A) $
]

#proposition(title: "A Global Discriminant as a Product of Local Ones")[
  For every nonzero prime $frak(p) subset.eq A$,

  $ "Disc"_(B slash A) hat(A)_frak(p)
    =product_(frak(q)|frak(p))
      "Disc"_(hat(B)_frak(q) slash hat(A)_frak(p)) $
]

#proof[
  By localization we may assume that $A$ is a DVR. The completed algebra and
  its integral model decompose as

  $ L ⊗_K K_frak(p) tilde.eq product_(frak(q)|frak(p)) L_frak(q),
    quad
    B ⊗_A hat(A)_frak(p) tilde.eq
      product_(frak(q)|frak(p)) hat(B)_frak(q) $

  Choose an $hat(A)_frak(p)$-basis in each factor and concatenate the bases.
  Distinct factors multiply to zero, so the trace Gram matrix is block
  diagonal. Its determinant is the product of the determinants of the blocks.
  Since completion is faithfully flat, the resulting ideal is exactly the
  completion of $"Disc"_(B slash A)$.
]

#remark(title: "Why It Is a Product")[
  Above one point $frak(p)$, the completed cover splits into its separate
  branches indexed by $frak(q)|frak(p)$. The trace pairing has no cross-terms
  between different branches. A block-diagonal determinant multiplies the
  branchwise discriminants, exactly as one expects for independent local
  contributions.
]

== Different versus Discriminant

The different is an ideal upstairs and the discriminant is an ideal
downstairs. Ideal norm is the bridge between them.

#theorem(title: [Discriminant--Different Formula])[
  In the $A K L B$ setup,

  $ "Disc"_(B slash A)="N"_(B slash A) ("Diff"_(B slash A)) $
]

#proof[
  Both sides commute with localization, so it is enough to work over the DVR
  $A_(frak(p))$. There $B_(frak(p))$ is free. Write
  $e_1,dots,e_n$ for an $A$-basis of $B$, and let
  $e_1^∗,dots,e_n^∗$ be the trace-dual basis of $B^∗$:

  $ "Tr"_(L slash K) (e_i^∗ e_j)=delta_(i j) $

  If $e_i=sum_j a_(i j)e_j^∗$, then

  $ a_(i j)="Tr"_(L slash K) (e_i e_j) $

  Thus the trace Gram matrix is exactly the change-of-basis matrix from
  $B^∗$ to $B$. It follows that

  $ "Disc"_(B slash A)=[B^∗:B]_A $

  Chapter 4 related ideal norms and module indices. Since
  $(B:B^∗)=(B^∗)^(-1)="Diff"_(B slash A)$, that relation gives

  $ [B^∗:B]_A
    ="N"_(B slash A) ((B:B^∗))
    ="N"_(B slash A) ("Diff"_(B slash A)) $

  This proves the identity locally and hence globally.
]

#corollary(title: "The Discriminant Divisor Is the Pushforward of the Different Divisor")[
  Write

  $ "Diff"_(B slash A)=product_frak(q) frak(q)^(d_frak(q)) $

  Then

  $ "Disc"_(B slash A)
    =product_frak(p) frak(p)^(
      sum_(frak(q)|frak(p))
      f_(frak(q) slash frak(p)) d_frak(q)) $

  Equivalently, for the finite map
  $pi:"Spec" B->"Spec" A$,

  $ "div"("Disc"_(B slash A))
    =pi_* "div"("Diff"_(B slash A)) $
]

#proof[
  Apply the prime-ideal norm formula from Chapter 4 to the factorization of
  the different:

  $ "N"_(B slash A) (frak(q))
    =frak(p)^(f_(frak(q) slash frak(p))) $

  and use multiplicativity of the ideal norm.
]

#quote[
  #emph[Geometric dictionary.] The different divisor is the ramification
  divisor on the source. The discriminant divisor is its pushforward, hence
  the branch divisor on the base.
]

#remark(title: "Different Exponent and Discriminant Exponent")[
  The number

  $ d_frak(q):=v_frak(q) ("Diff"_(B slash A)) $

  is the #emph[different exponent] at $frak(q)$. Downstairs one sees only the
  weighted sum

  $ v_frak(p) ("Disc"_(B slash A))
    =sum_(frak(q)|frak(p)) f_(frak(q) slash frak(p))d_frak(q) $

  The residue degrees occur because pushing a closed point $[frak(q)]$ to
  $[frak(p)]$ multiplies its degree by
  $[B slash frak(q):A slash frak(p)]$.
]

== Detecting Ramification

=== The Trace Criterion over a Field

#lemma(title: "Finite Etale Algebras and the Discriminant")[
  Let $k$ be a field and let $R$ be a finite-dimensional commutative
  $k$-algebra with basis $r_1,dots,r_n$. Then the following are equivalent:

  + $R$ is a finite etale $k$-algebra;

  + the trace pairing $(x,y) mapsto "Tr"_(R slash k) (x y)$ is perfect;

  + $"disc"(r_1,dots,r_n)!=0$.
]

#proof[
  The equivalence of the first two conditions was established in Chapter 2:
  a finite commutative algebra over a field is etale exactly when its trace
  pairing is nondegenerate. Relative to the chosen basis, this pairing has
  Gram matrix

  $ ("Tr"_(R slash k) (r_i r_j))_(i,j) $

  A bilinear form over a field is nondegenerate exactly when its Gram
  determinant is nonzero, which is the third condition.
]

#theorem(title: "Ramified Primes Are Exactly the Prime Divisors of the Different and Discriminant")[
  Let $frak(q)|frak(p)$, and suppose that the residue extension
  $(B slash frak(q)) slash (A slash frak(p))$ is separable. Then

  $ frak(q) " is unramified"
    <=> frak(q) divides.not "Diff"_(B slash A) $

  Moreover,

  $ frak(p) " is unramified"
    <=> frak(p) divides.not "Disc"_(B slash A) $
]

#proof[
  We first prove the statement downstairs. Localize at $frak(p)$. The
  $A_(frak(p))$-module $B_(frak(p))$ is free; choose a basis
  $e_1,dots,e_n$. Reducing it modulo $frak(p)$ gives a basis of

  $ R:=B slash frak(p)B $

  over $k:=A slash frak(p)$. Trace commutes with reduction, so

  $ "disc"_R (overline(e)_1,dots,overline(e)_n)
    =overline("disc"_B (e_1,dots,e_n)) $

  Therefore $frak(p)$ divides $"Disc"_(B slash A)$ exactly when the trace
  pairing on $R$ is degenerate. By the preceding lemma, this happens exactly
  when $R$ is not finite etale over $k$.

  Now factor

  $ frak(p)B=product_(i=1)^r frak(q)_i^(e_i) $

  The Chinese remainder theorem gives

  $ B slash frak(p)B
    tilde.eq product_(i=1)^r B slash frak(q)_i^(e_i) $

  This algebra is finite etale over $k$ exactly when each $e_i=1$ and every
  residue extension is separable, which is precisely unramifiedness over
  $frak(p)$.

  For the upstairs statement, complete at $frak(q)$ and $frak(p)$. There is
  only one prime upstairs, and the norm formula reads

  $ "N"_(hat(B)_frak(q) slash hat(A)_frak(p)) (frak(q)^m)
    =frak(p)^(f_frak(q) m) $

  Hence the local different is divisible by $frak(q)$ exactly when its
  discriminant is divisible by $frak(p)$. The downstairs result finishes the
  proof.
]

#remark(title: "Fiberwise Meaning")[
  The closed fiber

  $ "Spec"(B slash frak(p)B)->"Spec"(A slash frak(p)) $

  is etale precisely when its trace pairing is perfect. A ramification index
  $e_frak(q)>1$ produces nilpotent thickness at the point $frak(q)$; an
  inseparable residue extension produces a non-etale reduced point. The
  discriminant detects both failures through one determinant.
]

#corollary(title: "Only Finitely Many Primes Ramify")[
  Only finitely many primes of $A$, and only finitely many primes of $B$,
  ramify in $L slash K$.
]

#proof[
  A nonzero ideal of a Dedekind domain has only finitely many prime divisors.
  The ramified primes of $A$ are the prime divisors of
  $"Disc"_(B slash A)$, and the ramified primes of $B$ are the prime divisors
  of $"Diff"_(B slash A)$.
]

== Discriminants of Orders

Let $C subset.eq B$ be an $A$-order in $L$: it is an $A$-subalgebra that is
also an $A$-lattice. Its normalization is $B$, and its conductor is

$ frak(f)_(B slash C)=(C:B)={x in B | x B subset.eq C} $

The geometry from Chapter 4 should be kept in mind:
$"Spec" B->"Spec" C$ is the normalization of an arithmetic curve, and the
conductor is supported where this normalization is not an isomorphism.

#definition(title: "Discriminant of an Order")[
  The discriminant ideal of an $A$-order $C$ is

  $ "Disc"_(C slash A):="Disc"(C) $

  Since $C subset.eq B$, one has

  $ "Disc"_(C slash A) subset.eq "Disc"_(B slash A) $
]

#theorem(title: [Index--Discriminant Formula])[
  For every $A$-order $C subset.eq B$,

  $ "Disc"_(C slash A)
    =[B:C]_A^2 "Disc"_(B slash A) $
]

#proof[
  This is the change-of-lattice formula with $M=B$ and $N=C$. To see the
  mechanism directly, localize at each prime $frak(p)$ of $A$. Choose a basis
  $e$ of $B_(frak(p))$ and write a basis of $C_(frak(p))$ as $e P$. Then

  $ "disc"(e P)=det(P)^2 "disc"(e) $

  while $det(P)$ generates $[B:C]_A A_(frak(p))$. The local identities glue
  to the displayed global ideal identity.
]

#corollary(title: "A Squarefree Power Discriminant Gives the Maximal Order")[
  Let $A=ZZ$, let $L=QQ(alpha)$, and suppose $alpha$ is an algebraic integer
  with minimal polynomial $f$. If $"disc"(f)$ is squarefree, then

  $ cal(O)_L=ZZ[alpha], quad d_L="disc"(f) $
]

#proof[
  The power order $C=ZZ[alpha]$ has basis
  $1,alpha,dots,alpha^(n-1)$, so

  $ "Disc"_(C slash ZZ)=("disc"(f)) $

  The index--discriminant formula for $B=cal(O)_L$ becomes

  $ "disc"(f)=[B:C]^2 d_L $

  Any prime dividing the integer index $[B:C]$ would occur in
  $"disc"(f)$ with exponent at least two. Squarefreeness therefore forces
  $[B:C]=1$.
]

#example(title: [$X^3-X-1$ Has Maximal Power Order])[
  Let $alpha^3-alpha-1=0$. Since

  $ "disc"(X^3-X-1)=-4(-1)^3-27(-1)^2=-23 $

  is squarefree,

  $ cal(O)_(QQ(alpha))=ZZ[alpha], quad d_(QQ(alpha))=-23 $

  The only ramified rational prime is $23$.
]

#remark(title: "Odd Valuation Forces Ramification")[
  For any prime $p$,

  $ v_p ("disc"(f))
    =2v_p ([cal(O)_L:ZZ[alpha]])+v_p (d_L) $

  Hence an odd value of $v_p ("disc"(f))$ forces $p|d_L$ and thus forces
  ramification. If $p$ does not divide $"disc"(f)$ at all, it is certainly
  unramified and the power order is already maximal at $p$.
]

=== The Role of the Conductor

#proposition(title: "Order Duals and the Conductor in the Monogenic Case")[
  Suppose $C=A[alpha]$ and $L=K(alpha)$. Let

  $ C^∗={x in L | "Tr"_(L slash K) (x C) subset.eq A} $

  and let $frak(f)=frak(f)_(B slash C)$. Then

  $ frak(f)=(B^∗:C^∗) $

  If one defines the $B$-ideal

  $ "Diff"_(C slash A)^(B):=(B:C^∗) $

  then

  $ "Diff"_(C slash A)^(B)=frak(f)"Diff"_(B slash A) $

  and

  $ "Disc"_(C slash A)
    ="N"_(B slash A) (frak(f))"Disc"_(B slash A) $
]

#proof[
  Trace duality reverses inclusions and satisfies $I^(∗∗)=I$. For
  $x in B$, one has

  $ x B subset.eq C
    <=> "Tr"_(L slash K) (x B C^∗) subset.eq A
    <=> x C^∗ subset.eq B^∗ $

  which proves $frak(f)=(B^∗:C^∗)$. Multiplying this colon identity by
  $(B^∗)^(-1)="Diff"_(B slash A)$ gives

  $ (B:C^∗)=frak(f)"Diff"_(B slash A) $

  For the monogenic order $C=A[alpha]$, the derivative computation proved
  below gives

  $ (B:C^∗)=(f'(alpha))B $

  Taking the ideal norm and using
  $"N"_(L slash K) (f'(alpha))=plus.minus "disc"(f)$ yields

  $ "Disc"_(C slash A)
    ="N"_(B slash A) ((B:C^∗))
    ="N"_(B slash A) (frak(f))"Disc"_(B slash A) $
]

#remark(title: "Conductor Formula: the Necessary Hypothesis")[
  The conductor formula in the preceding proposition is safe for a
  #emph[monogenic] order, which is the situation $C=A[alpha]$ used in the
  computation. For an arbitrary nonmonogenic order, the universal formula is

  $ "Disc"_(C slash A)=[B:C]_A^2 "Disc"_(B slash A) $

  and one must not silently replace $[B:C]_A^2$ by
  $"N"_(B slash A) (frak(f))$. These ideals always have the same support, but
  their multiplicities can differ.

  For example, if $B$ is a cubic ring of integers and
  $C=ZZ+m B$, then

  $ [B:C]=m^2, quad frak(f)=m B $

  so the two factors are $m^4$ and $"N"(m B)=m^3$, respectively. This
  distinction separates the lattice size of an order from the thickness of
  its normalization locus.
]

=== Dedekind's Index Criterion

When $"disc"(f)$ is not squarefree, one needs a local test deciding whether a
prime dividing the polynomial discriminant also divides the index of the
power order.

#theorem(title: "Dedekind's Index Criterion")[
  Let $L=QQ(alpha)$, let $f in ZZ[X]$ be the monic minimal polynomial of
  $alpha$, and fix a rational prime $p$. Factor

  $ overline(f)=product_(i=1)^r overline(phi)_i^(e_i) in FF_p[X] $

  with distinct monic irreducible $overline(phi)_i$. Choose monic lifts
  $phi_i in ZZ[X]$ and put

  $ g:=product_(i=1)^r phi_i $

  Choose a monic lift $h$ of
  $overline(f) slash overline(g)$ and define

  $ F:=(g h-f)/p in ZZ[X] $

  Then

  $ p divides.not [cal(O)_L:ZZ[alpha]]
    <=> "gcd"(overline(g),overline(h),overline(F))=1 $

  Equivalently, $p$ divides the index exactly when the three reductions have
  a #emph[nonconstant] common factor.
]

#proof[
  Put $R=ZZ_(p)[alpha]$. The rational prime $p$ does not divide the global
  index exactly when $R$ is the integral closure of $ZZ_(p)$ in $L$.
  Reduction modulo $p$ identifies

  $ R slash p R tilde.eq FF_p[X] slash (overline(f)) $

  and its nilradical is generated by the image of $overline(g)$. Thus the
  radical of $p R$ is

  $ J=(p,g(alpha)) $

  A standard one-dimensional maximality test says that $R$ is
  $p$-maximal exactly when the multiplier ring

  $ (J:J):={x in L | x J subset.eq J} $

  equals $R$. Indeed, any proper overorder at $p$ enlarges the multiplier ring
  of the radical, while an element of $(J:J) slash R$ is integral and creates
  such an overorder.

  It remains to compute $(J:J)$. Write an element whose denominator is $p$
  as $a(alpha)/p$, with $deg(a)<deg(f)$. The conditions

  $ (a(alpha)/p)p in J, quad
    (a(alpha)/p)g(alpha) in J $

  reduce, after using $g h-f=p F$, to the existence of a nonzero polynomial
  class divisible simultaneously by
  $overline(g)$, $overline(h)$, and $overline(F)$. Polynomial division in
  $FF_p [X]$ therefore gives

  $ (J:J)!=R
    <=> "gcd"(overline(g),overline(h),overline(F))!=1 $

  Combining this computation with the maximality test proves the criterion.
]

#remark(title: "Do Not Reverse the Criterion")[
  The direction is worth memorizing: #emph[no common factor means no index
  obstruction]. A nonconstant common factor produces an element with a
  denominator $p$ that is integral over the power order, so the order was too
  small at $p$.
]

#remark(title: "How the Criterion Is Used")[
  Start with $C=ZZ[alpha]$ and factor $"disc"(f)$. Only its prime divisors can
  divide $[cal(O)_L:C]$. Apply Dedekind's criterion to each such prime. If an
  obstruction appears, adjoin the resulting integral element with denominator
  $p$ to obtain a larger order and repeat. This is the conceptual core of the
  round-two or Pohst--Zassenhaus method for computing rings of integers.
]

== Computing the Different and Discriminant

=== The Monogenic Formula

The easiest case is also the most important local case: the integral closure
is generated by one element.

#lemma(title: "The Basic Trace Identity")[
  Let $L=K(alpha)$, let $f in A[X]$ be the monic minimal polynomial of
  $alpha$, and put $n=deg(f)$. Then

  $ "Tr"_(L slash K) (alpha^m/f'(alpha))
    =cases(0 & 0<=m<=n-2,
           1 & m=n-1,
           "an element of " A quad  & m>=n) $
]

#proof[
  Let $alpha_1,dots,alpha_n$ be the roots of $f$ in a splitting field. The
  partial-fraction decomposition is

  $ 1/f(X)=sum_(i=1)^n 1/(f'(alpha_i)(X-alpha_i)) $

  Expanding at infinity gives

  $ 1/f(X)
    =sum_(m>=0)(sum_(i=1)^n alpha_i^m/f'(alpha_i))X^(-m-1) $

  On the other hand, since $f$ is monic,

  $ 1/f(X)=X^(-n)(1+c_1 X^(-1)+c_2 X^(-2)+dots) $

  with every $c_i in A$. Comparing coefficients of $X^(-m-1)$ gives $0$
  before $m=n-1$, gives $1$ at $m=n-1$, and gives an element of $A$
  thereafter. The inner sum is exactly
  $"Tr"_(L slash K) (alpha^m/f'(alpha))$.
]

#theorem(title: "Different of a Monogenic Integral Closure")[
  Suppose $B=A[alpha]$, and let $f in A[X]$ be the minimal polynomial of
  $alpha$. Then

  $ B^∗=1/f'(alpha) B $

  and therefore

  $ "Diff"_(B slash A)=(f'(alpha)) $
]

#proof[
  Every product of two elements of $B=A[alpha]$ can be reduced modulo $f$ to
  a polynomial $r(alpha)$ with $r in A[X]$ and $deg(r)<n$. The trace identity
  says that

  $ "Tr"_(L slash K) (r(alpha)/f'(alpha)) in A $

  Consequently,

  $ 1/f'(alpha) B subset.eq B^∗ $

  Inverting reverses the inclusion and gives

  $ "Diff"_(B slash A) subset.eq (f'(alpha)) $

  The two ideals have the same norm. Indeed,

  $ "N"_(B slash A) ("Diff"_(B slash A))
    ="Disc"_(B slash A)=("disc"(f)) $

  while the resultant formula gives

  $ "N"_(B slash A) ((f'(alpha)))=("disc"(f)) $

  An inclusion of nonzero ideals of a Dedekind domain with equal norm has
  equal valuation at every prime. Hence equality holds, and taking inverses
  also yields the formula for $B^∗$.
]

#remark(title: "Jacobian and Kahler Differentials")[
  The presentation $B=A[X] slash (f)$ gives

  $ Omega_(B slash A)^1
    tilde.eq B slash (f'(alpha)) "d"alpha $

  Therefore

  $ "Ann"_B (Omega_(B slash A)^1)
    ="Fitt"_0^B (Omega_(B slash A)^1)
    =(f'(alpha))="Diff"_(B slash A) $

  This is the one-dimensional Jacobian criterion in arithmetic form.
  Where $f'(alpha)$ is a unit, infinitesimal lifting is unique and the map is
  etale. Where it vanishes, relative differentials survive and the map
  ramifies.
]

#quote[
  The derivative $f'(alpha)$ is not an accidental computational trick: it is
  the Jacobian of the finite map $"Spec" B->"Spec" A$.
]

#example(title: [The Different of $QQ(i)$])[
  For $B=ZZ[i]=ZZ[X] slash (X^2+1)$,

  $ f'(i)=2i $

  Hence

  $ "Diff"_(ZZ[i] slash ZZ)=(2i)=(2)=(1+i)^2 $

  and its norm is $(4)$, agreeing with the discriminant ideal. The exponent
  $2$ at $(1+i)$ records wild ramification above $2$.
]

#example(title: "A Tame Eisenstein Extension")[
  Let $A$ be a complete DVR with uniformizer $pi_A$ and residue
  characteristic $p$. Suppose $p divides.not e$ and let

  $ L=K(pi), quad pi^e=pi_A $

  The polynomial $X^e-pi_A$ is Eisenstein, so $B=A[pi]$. Since

  $ f'(pi)=e pi^(e-1) $

  and $e$ is a unit, one has

  $ "Diff"_(B slash A)=(pi)^(e-1) $

  Thus a tame totally ramified extension contributes exactly $e-1$ to the
  ramification divisor.
]

=== Elementwise Differents

Even when $B$ is not globally monogenic, all primitive integral elements
together generate the different.

#definition(title: "Different of an Element")[
  For $alpha in B$ with minimal polynomial $f_alpha in A[X]$, define

  $ delta_(B slash A) (alpha)
    :=cases(f'_alpha (alpha) quad & L=K(alpha),
            0 & L!=K(alpha)) $
]

#theorem(title: "The Different Is Generated by Elementwise Differents")[
  One has

  $ "Diff"_(B slash A)
    =(delta_(B slash A) (alpha):alpha in B) $
]

#proof[
  Let $J$ denote the ideal on the right. If $alpha$ is primitive, put
  $C=A[alpha]$. Since $B^∗ subset.eq C^∗$,

  $ (B:C^∗) subset.eq (B:B^∗)="Diff"_(B slash A) $

  The monogenic calculation gives
  $(B:C^∗)=(f'_alpha (alpha))B$, so every generator of $J$ lies in the
  different. Thus $J subset.eq "Diff"_(B slash A)$.

  For the reverse inclusion it is enough to localize at every prime
  $frak(q)$ of $B$. Complete at $frak(q)$ and
  $frak(p)=frak(q) inter A$. When the residue extension is separable, the
  complete integral closure is monogenic:

  $ hat(B)_frak(q)=hat(A)_frak(p)[beta] $

  The monogenic theorem says that the completed different is generated by
  $f'_beta (beta)$. By density and weak approximation, choose
  $alpha in B$ arbitrarily close to $beta$ at $frak(q)$ and simultaneously
  away from the finitely many conjugate collision loci. Krasner's lemma then
  ensures $K(alpha)=L$, while sufficient closeness preserves the valuation of
  the derivative. Hence some $delta_(B slash A) (alpha)$ generates the same
  localized ideal as the different at $frak(q)$.

  In the general residue-field case, first make a finite etale residue
  extension and descend the equality by faithful flatness. Thus
  $J_(frak(q))="Diff"_(B slash A)_(frak(q))$ for every $frak(q)$, and the
  two ideals are equal.
]

#remark(title: "Local Monogenicity versus Global Monogenicity")[
  A number field need not admit a power integral basis, so one should not
  expect one element $alpha$ to generate $B$ globally. The theorem says that
  the different is nevertheless #emph[locally] generated by derivatives of
  suitable primitive elements. This is an ideal-theoretic way to glue local
  Jacobians without choosing a global equation.
]

=== Different Exponents and Tame Ramification

#theorem(title: "Bounds for the Different Exponent")[
  Let $frak(q)|frak(p)$ and suppose the residue extension is separable. Put

  $ e=e_(frak(q) slash frak(p)), quad
    d_frak(q)=v_frak(q) ("Diff"_(B slash A)) $

  Then

  $ e-1<=d_frak(q)<=e-1+v_frak(q) (e) $

  Moreover,

  $ d_frak(q)=e-1 <=> frak(q) " is tamely ramified" $
]

#proof[
  Localization and completion do not change $e$ or $d_frak(q)$, so pass to
  complete DVRs. Let $E slash K$ be the maximal unramified subextension. Its
  different is the unit ideal, and $L slash E$ is totally ramified of degree
  $e$. Thus it suffices to treat a totally ramified extension with separable
  residue field.

  Choose a uniformizer $pi$ of $L$. Then $B=A_E [pi]$, and its minimal
  polynomial

  $ f(X)=X^e+a_(e-1)X^(e-1)+dots+a_1 X+a_0 $

  is Eisenstein over $A_E$. The monogenic formula gives

  $ d_frak(q)=v_frak(q) (f'(pi)) $

  Since $v_frak(q) (a_i)>=e$ for $i<e$, differentiation shows

  $ f'(pi)=e pi^(e-1)+sum_(i=1)^(e-1) i a_i pi^(i-1) $

  The first term has valuation $e-1+v_frak(q) (e)$, while every remaining
  term has valuation at least $e$. It follows immediately that
  $d_frak(q)>=e-1$. If $e$ is prime to the residue characteristic, the first
  term has the unique smallest valuation $e-1$, so $d_frak(q)=e-1$.
  If the residue characteristic divides $e$, every term has valuation at
  least $e$, so $d_frak(q)>e-1$.

  For the upper bound, use the local trace-dual estimate for an Eisenstein
  extension:

  $ v_frak(q) (f'(pi))<=e-1+v_frak(q) (e) $

  Here is the mechanism. Apply the trace identity to
  $1,pi,dots,pi^(e-1)$ and put the trace matrix into elementary-divisor form
  over the base DVR. The last dual vector is $1/f'(pi)$; comparing its
  denominator with the trace of $1$, which is $e$, shows that its pole order
  cannot exceed $e-1+v_frak(q) (e)$. Equivalently, the last elementary divisor
  of the trace lattice is bounded by the valuation of $e pi^(e-1)$.
  This proves the upper estimate.

  Finally, under the separable-residue hypothesis, tameness is exactly the
  condition that the residue characteristic does not divide $e$, equivalently
  $v_frak(q) (e)=0$. The preceding valuation comparison proves the final
  equivalence.
]

#remark(title: "Reading the Inequality")[
  The baseline $e-1$ is the geometric multiplicity forced by bringing $e$
  sheets together. The additional amount

  $ d_frak(q)-(e-1) $

  is the #emph[wild contribution]. Tame ramification has no extra
  infinitesimal thickness; wild ramification does.
]

#example(title: "The Upper Bound Can Be Sharp")[
  Over $QQ_p$, let $pi^p=p$. The polynomial $X^p-p$ is Eisenstein, so the
  extension is totally and wildly ramified of degree $p$. Since

  $ f'(pi)=p pi^(p-1), quad v_pi (p)=p $

  one obtains

  $ d=v_pi (f'(pi))=2p-1=(p-1)+v_pi (p) $

  Thus the upper bound is attained.
]

#remark(title: "Equal Characteristic Can Be Much Wilder")[
  In characteristic $p$, the symbol $v_frak(q) (e)$ is infinite when
  $p|e$, so the upper estimate imposes no finite bound. For example, the
  Eisenstein Artin--Schreier-type family over $FF_p((t))$ defined by

  $ X^p+t^m X+t $

  has derivative $t^m$ and different exponent growing with $m$. Wild
  ramification is therefore not merely a slightly larger version of tame
  ramification; in equal characteristic its depth can be arbitrarily large.
]

=== Towers

#theorem(title: "Transitivity of the Different")[
  Let $M slash L slash K$ be a tower of finite separable extensions. Let $C$
  be the integral closure of $B$ in $M$. Then, as ideals of $C$,

  $ "Diff"_(C slash A)
    ="Diff"_(C slash B) "Diff"_(B slash A) C $
]

#proof[
  Trace is transitive:

  $ "Tr"_(M slash K)
    ="Tr"_(L slash K) compose "Tr"_(M slash L) $

  Let $J$ be a fractional $B$-ideal. The set

  $ {x in M | "Tr"_(M slash L) (x C) subset.eq J} $

  is $J C$ times the codifferent $C^∗_(C slash B)$. This may be checked after
  localizing $B$, where $J$ is principal and the assertion follows by pulling
  its generator through the trace. Taking
  $J=B^∗_(B slash A)$ and using transitivity gives

  $ C^∗_(C slash A)
    =C^∗_(C slash B) B^∗_(B slash A) C $

  All these fractional ideals are invertible. Inverting the equality yields
  the formula for differents.
]

#corollary(title: "Tower Formula for Discriminants")[
  In the same setup,

  $ "Disc"_(C slash A)
    ="Disc"_(B slash A)^[M:L]
      "N"_(B slash A) ("Disc"_(C slash B)) $
]

#proof[
  Take the ideal norm of the different tower formula. Norms in a tower are
  transitive, and extending a $B$-ideal $I$ to $C$ satisfies

  $ "N"_(C slash B) (I C)=I^[M:L] $

  Therefore

  $ "N"_(C slash A) ("Diff"_(C slash A))
    ="N"_(B slash A) ("Diff"_(B slash A)^[M:L]
      "N"_(C slash B) ("Diff"_(C slash B))) $

  Replace each norm of a different by the corresponding discriminant.
]

#corollary(title: "Ramification in a Tower")[
  A prime $frak(p)$ of $A$ ramifies in $M slash K$ exactly when at least one
  of the following occurs:

  + $frak(p)$ ramifies in $L slash K$;

  + some $frak(q)|frak(p)$ ramifies in $M slash L$.

  Equivalently, the ramified primes of $M slash K$ divide either
  $"Disc"_(B slash A)$ or
  $"N"_(B slash A) ("Disc"_(C slash B))$.
]

#proof[
  Ramification indices multiply in a tower, and residue extensions compose;
  this proves the first statement directly. The discriminant tower formula
  gives the ideal-theoretic version: a prime divides the product exactly when
  it divides one of the two factors.
]

== A Compact Dictionary

#table(
  columns: (1fr, 1.3fr, 1.5fr),
  align: (left, center, left),
  stroke: (x, y) => if y == 1 { (top: 0.8pt + rgb("#555555")) } else { none },
  inset: (x: 8pt, y: 5pt),
  table.header(
    [#emph[Object]],
    [#emph[Formula]],
    [#emph[Meaning]],
  ),
  [Codifferent],
  [$B^∗={x | "Tr"(x B) subset.eq A}$],
  [The trace-dual lattice],
  [Different],
  [$"Diff"_(B slash A)=(B^∗)^(-1)$],
  [Ramification divisor upstairs],
  [Discriminant],
  [$"Disc"_(B slash A)="N"("Diff")$],
  [Branch divisor downstairs],
  [Monogenic case],
  [$"Diff"=(f'(alpha))$],
  [Jacobian or infinitesimal defect],
  [Local exponent],
  [$e-1<=d<=e-1+v(e)$],
  [$d=e-1$ exactly in the tame case],
)

#quote[
  The trace pairing turns separability into linear algebra; the different
  turns its integral defect into a divisor; the discriminant records the
  shadow of that divisor on the base.
]
