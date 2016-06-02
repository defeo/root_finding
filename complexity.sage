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

BigFieldDiv = BigFieldMul * log(n)

def Mnot(k):
    return k* log(k)* log(log(k))

def PolynomialAdd(deg):
    return BigFieldAdd * deg 

def PolynomialMul(deg):
    if ARITHMETIC == "FAST":
        return BigFieldMul * Mnot(deg)
    else:
        return BigFieldMul * deg^2

def PolynomialGCD(deg1,deg2):
    if ARITHMETIC == "FAST":
        deg = max(deg1,deg2)
        return Mnot(deg*n)*log(deg) + d*Mnot(n)*log(n)     # theorem 11.5 Von Zur Gathen M(dn)log(d) + dM(n) log(n)      # simplifies to PolynomialMul(deg) * log(d*n)     
    else:
        return BigFieldMul * deg1 * deg2

def MultiEvaluation(deg):
    return log(deg)*PolynomialMul(deg)



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
    TraceModF = n* log(q) * PolynomialMul(d)         # does not take into account fast modular composition
    if COMPLEXITY_TYPE == "WORST":
        h = n
    else:
        h = log(d)
    BTA = h *  (TraceModF + q* PolynomialGCD(d,d))
    return expand(BTA)
print "BTA costs:  ",  BTA(n,d)




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
print "SRA costs (version in original paper):  ", SRA



# new algo (question marks corresponding to LIX probabilistic and SRA): SRA computation up to n-log(d), then exhaustive search, then descent
# reuse first_step from above (n*resultant should be replaced by (n-log(d)) but we suppose that is negligible)
# reuse multievalGCD
testRoots = MultiEvaluation(d)
second_step = n*multievalGCD
questionMarksAlgo = first_step + testRoots + second_step
print "New algorithm costs: (note that this algorithm is probabilistic) ", questionMarksAlgo






# ARM analysis
# Original MOV version as described in Christophe's document ... not very clear
precomputation = n^2 * log(q) * BigFieldMul
leastAffineMultiple = d * log(q) * PolynomialMul(d) + d^omega * BigFieldMul
def AffineGCD(deg1,deg2):
    return PolynomialGCD(deg1,deg2)
powerModF = n * log(q) * PolynomialMul(d)     #lines 3-4 in Algorithm 5         # assumes n>d here
if COMPLEXITY_TYPE == "WORST":
    h = n
else:
    h = log(d)            # use submultiplicative argument here
LinearizedPolEvaluation = n*log(q)*BigFieldMul
Mirho = 2*LinearizedPolEvaluation + PolynomialAdd(d)         # line 9 in Algorithm 5
Mirhotilde = d*n*BigFieldMul                              # line 10 in Algorithm 5
Mirhohat = AffineGCD(d,d)                                 # line 11 in Algorithm 5
firho = d*log(q)*PolynomialMul(d) + PolynomialGCD(d,d)    # had to guess line 12 in Algorithm 5. The guess is a trace-like computation (but only up to d), then a cgd
steps6to16 = h*q*(Mirho+Mirhotilde+Mirhohat+firho)
ARM = precomputation + leastAffineMultiple + powerModF + steps6to16
print "ARM costs (version in Christophe's July 2015 draft):  ",ARM



