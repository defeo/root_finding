# -*- encoding: utf-8

from sage.matrix.constructor import matrix
from sage.modules.free_module_element import zero_vector, vector
from sage.modules.free_module import VectorSpace
from sage.rings.arith import power_mod
from collections import namedtuple
from sage.misc.misc_c import prod
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from itertools import izip_longest

from sage.libs.ntl.extra import ntl_switch_vars, ntl_interpolate, ntl_eval_vec, ntl_eval_prod, ntl_eval_roots

class Tree:
    '''
    This class represents a product tree.
    '''
    def __init__(self, val, parent=None):
        self.children = []
        self._parent = parent
        self.val = val
        self.girth = 1
    
    def parent(self):
        if self._parent and len(self._parent.children) == 1:
            return self._parent.parent()
        return self._parent

    def is_leaf(self):
        return not self.children
    
    def __getitem__(self, i):
        return self.children[i]

    def __iter__(self):
        '''
        depth first walk, "skimming" through "filaments"
        '''
        if len(self.children) == 1:
            for c in self.children[0].__iter__():
                yield c
        else:
            # We save the list of children, to avoid
            # walking children added after iteration.
            children = self.children[:]
            yield self
            for c in children:
                for d in c.__iter__():
                    yield d

                
    def add_child(self, val):
        if self.children:
            self._enlarge()
        c = Tree(val, self)
        self.children.append(c)
        return c

    def _enlarge(self, n=1):
        self.girth += n
        if self._parent:
            self._parent._enlarge(n)
            
    def prune(self):
        '''
        Remove node from tree, and its ancestry up to first node with
        at least one child left.

        Returns lowest node left in ancestry, or None if all tree was
        pruned.
        '''
        if self._parent:
            self._parent.children.remove(self)
            if not self._parent.children:
                return self._parent.prune()
            else:
                self._parent._enlarge(-1)
                return self._parent
        else:
            return None

def gammas(basis):
    '''
    Compute the γ_i,j = L_i(v_j) from a basis.
    '''

    K = basis[0].parent()
    p = K.characteristic()
    n = K.degree()
    assert n == len(basis)

    # Uses the plain recursive definition of L_i.
    # Complexity is evidently O(n² log p) mulitpilication in K.
    gammas = matrix(K, n, n)
    gammas.set_row(0, basis)
    for i in range(1, n):
        a = gammas[i-1, i-1]**(p-1)
        for j, v in enumerate(basis):
            g = gammas[i-1, j]
            gammas[i, j] = g**p - a * g
    return gammas

def arm(f, basis=None):
    '''Computes the roots of f using the Affine Refinement Method.
    
    `basis` is the vector space basis of the base field used to define
    the affine geometry of GF(q). If none, the standard monomial basis
    is used.
    '''
    
    K = f.base_ring()
    Fp = K.prime_subfield()
    X = f.parent().gen()
    z = K.gen()
    p = K.characteristic()
    n = K.degree()

    gs = gammas(basis if basis else [z**i for i in range(n)])

    # Compute L_i(X) mod f recursively.  If d = deg f, and M(d) is the
    # cost of multiplying polynomials with coefficients in K,
    # complexity is O(n M(d) log p) operations over K.
    L = [X]
    for i in range(n):
        L.append(power_mod(L[-1], p, f) - gs[i][i]**(p-1) * L[-1])

    # roots is a list of pairs (factor of f, approximation to its roots)
    # it is intialized to f mod X^(p^n) - X and the zero approximation (any root)
    Node = namedtuple('Node', ['f', 'approx', 'L'])
    tree = Tree(Node(f.gcd(L.pop()), zero_vector(Fp, n), None))
    roots = []
    
    # We descend the product tree
    for i, l, g in reversed(zip(range(n), L, gs)):
        beta = g[i]
        # We consider each known factor with its approximation
        for node in tree:
            parent = node.parent()
            if parent:
                tmpl = parent.val.L % node.val.f
            else:
                tmpl = l
            node.val = Node(node.val.f, node.val.approx, tmpl)
            if node.is_leaf():
                dot = g.dot_product(node.val.approx)
                f = node.val.f
                d = f.degree()
                for c in Fp:
                    nf = f.gcd(tmpl - dot - c*beta)
                    if not nf.is_constant():
                        if nf.degree() == 1:
                            roots.append(-nf.monic().constant_coefficient())
                            d -= 1
                        else:
                            nr = zero_vector(Fp, n)
                            nr[i] = c
                            node.add_child(Node(nf, node.val.approx + nr, None))
                            d -= nf.degree()
                        f //= nf
                        if f.degree() == 1:
                            roots.append(-f.monic().constant_coefficient())
                            d -= 1
                            break
                        elif f.is_constant():
                            break
                        tmpl %= f
                # If we haven't added any children, this node has been
                # completely factored and can be pruned.
                # If the tree is left empty, done.
                if node.is_leaf() and node.prune() is None:
                    return roots
    return roots
                
def _my_dot_prod(v, elt):
    """
    same as v.dot_product(elt), just way faster.
    """
    return sum((y for x, y in zip(v, elt) for _ in range(x)),
               elt.base_ring().zero())

def _avoid_b(b, l):
    '''
    Returns a list of l elements whose span does not contain b.
    '''
    K = b.base_ring()
    n = K.degree()
    P = b.parent()
    p = K.characteristic()

    z = P(K.gen())
    v = P.one()
    
    points = [P.zero()]
    l -= 1
    skip = b[0].polynomial().degree()
    for i in range(n):
        if i == skip:
            v *= z
        for j in range(p-1):
            for k in range(j * p**i, (j+1) * p**i):
                points.append(points[k] + v)
                l -= 1
                if l <= 0:
                    return points
        v *= z
                    
    
def resultant(f, b):
    '''
    Computes the resultant

      Res_x(f(x), y - x^p + b^(p-1)x)
    '''

    K = f.base_ring()
    z = K.gen()
    n = K.degree()
    Fp = K.prime_subfield()
    P = f.parent()
    X = P.gen()
    p = K.characteristic()
    d = f.degree()
    assert(b.parent() is P)
    assert(d < K.cardinality() // p)
    a = b**(p-1)

    points = _avoid_b(b, d+1)
    projs = [pt**p - a*pt for pt in points]
    
    evals = multieval(f, b, points, projs)

    return (-1)**(d % 2) * ntl_interpolate(projs, evals)

def _multieval(f, a, points):
    '''
    Private subroutine used by `multieval` and `multiroots`.

    Returns the list 

       [f mod X^p - aX - D  for D in points]

    '''
    K = f.base_ring()
    Fp = K.prime_subfield()
    P = f.parent()
    X = P.gen()
    PP = PolynomialRing(P, 'Y')
    Y = PP.gen()
    p = K.characteristic()
    d = f.degree()
    assert(a.parent() is P)
    
    # Compute f mod [ Y - (X^p - a X) ]
    # recursively by divide and conquer
    lins = [X**p - a*X]
    while lins[-1].degree() < d // 2:
        lins.append(lins[-1]**2)

    fY = PP(f)
    for i, l in reversed(list(enumerate(lins))):
        nfY = PP(0)
        for j, coeff in enumerate(fY):
            q, r = coeff.quo_rem(l)
            nfY += PP(r).shift(j)
            nfY += PP(q).shift(j+2**i)
        fY = nfY

    # Now we use very naive algorithms for eval, to avoid automatic
    # copying back and forth between NTL and Pari.
    #
    # This should be improved by forcing NTL everywhere
    #eval = lambda pol, pt: sum(c*pt**i for i, c in enumerate(pol))
    
    # express f as a polynomial with coefficients in Y rather than X
    fY = ntl_switch_vars(fY.list()) #list(izip_longest(*fY, fillvalue=K.zero()))
    
    # evaluate fY at Y=pt^p - a*pt for any point pt
    # (result is a list of polynomials in X)
    evals = [ntl_eval_vec(pol, points) for pol in fY] #[[eval(pol, pt) for pt in pgs] for pol in fY]
    return ntl_switch_vars(evals)
    
def multieval(f, b, points, projs=None):
    '''
    Multi-point evaluation with a twist :)

    Returns the list of evaluations

        [f(pt + c*b) for pt in points for c in GF(p)]

    where p is the characteristic of the base field.
    '''
    K = f.base_ring()
    Fp = K.prime_subfield()
    P = f.parent()
    p = K.characteristic()
    assert(b.parent() is P)

    a = b**(p-1)
    if projs is None:
        projs = [pt**p - a*pt for pt in points]
    evals = _multieval(f, a, projs)

    # evaluate each polynomial at each point and its shifted values
    return [ntl_eval_prod(p, d, b) for p, d in zip(evals, points)]

def multiroots(f, g, nr, roots, approx):
    '''Find the roots of f of the form 

      f(r + cb) = 0

    with r in roots and c in GF(p). g is the line of the matrix G
    corresponding to f.
    '''
    K = f.base_ring()
    Fp = K.prime_subfield()
    P = f.parent()
    p = K.characteristic()
    b = _my_dot_prod(nr, g)
    assert(b.parent() is P)

    a = b**(p-1)
    evals = _multieval(f, a, roots)

    newroots = []
    newapprox = []
    for pol, v in zip(evals, approx):
        d = _my_dot_prod(v, g)
        if pol.is_zero():
            cs = range(p)
        elif pol.degree() > 0:
            cs = ntl_eval_roots(pol, d, b)
        for c in cs:
            newroots.append(d + sum((b for _ in range(c)), P.zero()))
            newapprox.append(c*nr + v)

    return newroots, newapprox


def sra(f, basis=None):
    '''Computes the roots of f using the Successive Resultant Algorithm.
    
    `basis` is the vector space basis of the base field used to define
    the affine geometry of GF(q). If none, the standard monomial basis
    is used.
    '''

    K = f.base_ring()
    Fp = K.prime_subfield()
    P = f.parent()
    X = P.gen()
    z = K.gen()
    p = K.characteristic()
    n = K.degree()

    gs = gammas(basis if basis else [z**i for i in range(n)])
    #
    gs = gs.change_ring(P)

    # We project the roots via the L_i functions
    Fs = [f]
    depth = n - f.degree().ndigits(p) + 1
    for i, g in zip(range(depth-1), gs.diagonal()):
        Fs.append(resultant(Fs[-1], g))
            
    # We take all elements of the last subspace as candidate roots
    approx = [vector([0]*depth + list(v)) for v in VectorSpace(Fp, n-depth)]
    roots = [_my_dot_prod(v, gs[depth]) for v in approx]

    # We refine the roots by inverting the L_i functions
    for i, f in reversed(list(enumerate(Fs))):
        g = gs[i]
        nr = zero_vector(Fp, n)
        nr[i] = 1
        roots, approx = multiroots(f, g, nr, roots, approx)
    
    #
    return map(K, roots)

def bta(f):
    '''
    Berlekamp's Trace Algorithm, original version.
    '''
    if f.degree() == 1:
        return [-f[0]]
    elif f.is_constant():
        return []
    
    K = f.base_ring()
    Fp = K.prime_subfield()
    X = f.parent().gen()
    z = K.gen()
    p = K.characteristic()
    n = K.degree()

    # Compute Tr(ax) mod f
    a = K.random_element()
    aXp = a*X
    Tr = aXp
    for i in range(n-1):
        aXp = power_mod(aXp, p, f)
        Tr += aXp

    roots = []
    for c in Fp:
        nf = f.gcd(Tr - c)
        if not nf.is_constant():
            roots.extend(bta(nf))
            f = f // nf
            if f.degree() <= 1:
                roots.extend(bta(f))
                break
            Tr = Tr % f

    return roots

def not_so_good_bta(f):
    '''
    Berlekamp's Trace Algorithm, with an unsuccessful optimization via
    a subproduct tree.
    '''
    K = f.base_ring()
    Fp = K.prime_subfield()
    X = f.parent().gen()
    z = K.gen()
    p = K.characteristic()
    n = K.degree()

    # Product tree of f
    Node = namedtuple('Node', ['f', 'Tr'])
    tree = Tree(Node(f, None))
    roots = []

    while True:
        # We descend the product tree
        for node in tree:
            parent = node.parent()
            if parent is None:
                # Compute Tr(ax) mod f
                a = K.random_element()
                aXp = a*X
                Tr = aXp
                for i in range(n-1):
                    aXp = power_mod(aXp, p, node.val.f)
                    Tr += aXp
                node.val = Node(node.val.f, Tr)
            else:
                node.val = Node(node.val.f, parent.val.Tr % node.val.f)

            # If trace is constant, all node roots have the same
            # "twisted" trace. We will treat again this node.
            if node.is_leaf() and not node.val.Tr.is_constant():
                f = node.val.f
                Tr = node.val.Tr
                d = f.degree()
                for c in Fp:
                    nf = f.gcd(Tr - c)
                    if not nf.is_constant():
                        if nf.degree() == 1:
                            roots.append(-nf[0])
                            d -= 1
                        else:
                            node.add_child(Node(nf, None))
                            d -= nf.degree()
                        f = f // nf
                        if f.degree() == 1:
                            roots.append(-f[0])
                            d -= 1
                            break
                        elif f.is_constant():
                            break
                        Tr = Tr % f

                # If we haven't added any children, this node has been
                # completely factored and can be pruned.
                # If the tree is left empty, done.
                if node.is_leaf() and node.prune() is None:
                    return roots
