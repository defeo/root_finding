%var q,d,n,omega

# STANDARD OR FAST ARITHMETIC
ARITHMETIC = "FAST"              # Options are "FAST" and "STANDARD"
FAST_NORMAL_BASES = false
if ARITHMETIC == false:
    FAST_NORMAL_BASES = false

# WORST or AVERAGE case complexity
COMPLEXITY_TYPE = "WORST"        # Options are "WORST" and "AVERAGE"

# Respective size of parameters
DgeQ = true                         # default assumptions, some formulae may need changes otherwise

# linear algebra constant
#omega


# complexity of basic operations
SmallFieldAdd = 1         #log q
SmallFieldMul = 1         #log(q) * log(log(q))

BigFieldAdd = SmallFieldAdd * n

if ARITHMETIC == "FAST":
    BigFieldMul = SmallFieldMul * n * log(n) * log(log(n))
else:
    BigFieldMul = SmallFieldMul * n^2

def PolynomialAdd(deg):
    return BigFieldAdd * deg 

def PolynomialMul(deg):
    if ARITHMETIC == "FAST":
        return BigFieldMul * deg * log(deg)*log(log(deg))
    else:
        return BigFieldMul * deg^2

def PolynomialGCD(deg1,deg2):
    if ARITHMETIC == "FAST":
        deg = max(deg1,deg2)
        return BigFieldMul * deg * log(deg)*log(log(deg))
    else:
        return BigFieldMul * deg1 * deg2


# resolution Hilbert90 of small degree equations
# follows section 5.6 in Christophe's document
def Hilbert90(n,d):
    if ARITHMETIC == "FAST":
        if FAST_NORMAL_BASES:
                rightHandSide = n^1000                     # stupid answer to make sure error is detected; in fact must still be implemented
                systemSolving = n^1000                     # idem
        else:                                          # we suppose that we do not use normal bases here as the cost on multiplications would be too big
            rightHandSide = log(q) * BigFieldMul + BigFieldMul + BigFieldMul      # terms are for q powering, inversion using gcd, and muliplication, assuming a polynomial basis
            systemSolving = log(q) * n * BigFieldMul
    else:                                                 # here we assume normal bases
        rightHandSide = BigFieldMul                   # -q powering is O(1) assuming normal bases, only cost is for multiplication
        systemSolving = n * SmallFieldMul * log(n)         # system is circulant

    return rightHandSide + systemSolving                # stupid answer to make sure error is detected; in fact must still be implemented





# BTA analysis (change complexity type to WORST or AVERAGE if you want deterministic vs probabilistic complexity)
def BTA(n,d):
    TraceModF = n * log(q) *d
    if COMPLEXITY_TYPE == "WORST":
        h = n
    else:
        h = log(d)
    BTA = h *  (TraceModF + q* PolynomialGCD(d,d))
    return expand(BTA)
print BTA(n,d)





# SRA analysis
precomputation = n^2 * log(q) * BigFieldMul
resultant = (2*d + q^2) * BigFieldMul         # reduction of f coefficient-wise then Euclide algorithm
                                              # formula supposes d>q, may become (otilde of?) dq otherwise
first_step = n * resultant
multievalGCD = q * (d/q) * log(d/q) + d * q * log(q)         # following section 4.2 in SRA paper, first term is for computing F_{0,i}^{(j-1)}(x_j) using multipoint evaluation; second term is for d gcds of degree q polynomials
def SolveSmalldegree(n,d):
    return BTA(n,d)
    #return Hilbert90(n,d)
smalldegreeEquations = max(SolveSmalldegree(n,q)*d/q, SolveSmalldegree(n,2)*d/2)     # not totally accurate as considering 2 tradeofs only; in fact we can have any sum of BTA(n,d_i) with \sum_id_i=d
second_step = n*multievalGCD + smalldegreeEquations
SRA = expand(precomputation + first_step + second_step)





# ARM analysis
# Original MOV version as described in Christophe's document ... not very clear
precomputation = n^2 * log(q) * BigFieldMul
leastAffineMultiple = d^2 * log(q) + d^omega
def AffineGCD(deg1,deg2):
    return PolynomialGCD(deg1,deg2)
powerModF = (n-d) * log(q) * PolynomialMul(d)     #lines 3-4 in Algorithm 5
if COMPLEXITY_TYPE == "WORST":
    h = n
else:
    h = log(d)
LinearizedPolEvaluation = n*log(q)*BigFieldMul
Mirho = 2*LinearizedPolEvaluation + PolynomialAdd         # line 9 in Algorithm 5
Mirhotilde = d*n*BigFieldMul                              # line 10 in Algorithm 5
Mirhohat = AffineGCD(d,d)                                 # line 11 in Algorithm 5