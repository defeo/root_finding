?e3773947-6b5c-4496-bb74-754b8884cb3e?
# symbolic variables
%var q,d,n,omega,B


# Complexity model
# -----------------

# STANDARD OR FAST ARITHMETIC
ARITHMETIC = "FAST"              # Options are "FAST" and "STANDARD"
FAST_NORMAL_BASES = false
if ARITHMETIC == "STANDARD":
    FAST_NORMAL_BASES = false

# WORST or AVERAGE case complexity
COMPLEXITY_TYPE = "AVERAGE"        # Options are "WORST" and "AVERAGE"

# Respective size of parameters
#DgeQ = true                         # default assumptions, some formulae may need changes otherwise

# linear algebra constant
#omega

SmallFieldAdd = 1         #log q
SmallFieldMul = 1         #log(q) * log(log(q))

# smoothness bound on p-1
# B




# complexity of basic operations
# ------------------------------

BigFieldAdd = SmallFieldAdd * n


# M notation for multiplications
def Mnot(k):
    return k* log(k)* log(log(k))


if ARITHMETIC == "FAST":
    BigFieldMul = SmallFieldMul * Mnot(n)
else:
    BigFieldMul = SmallFieldMul * n^2

BigFieldDiv = BigFieldMul * log(n)
BigFieldExp = BigFieldMul * log(n)



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
    if ARITHMETIC == "FAST":
        return log(deg)*PolynomialMul(deg)
    else:
        return BigFieldMul * deg^2





# resolution Hilbert90 of small degree equations
# follows section 5.6 in Christophe's document
# def Hilbert90(n,d):
#     if ARITHMETIC == "FAST":
#         if FAST_NORMAL_BASES:
#                rightHandSide = n^1000                      stupid answer to make sure error is detected; in fact must still be implemented
#                systemSolving = n^1000                      idem
#        else:                                           we suppose that we do not use normal bases here as the cost on multiplications would be too big
#            rightHandSide = log(q) * BigFieldMul + BigFieldDiv + BigFieldMul       terms are for q powering, inversion using gcd, and muliplication, assuming a polynomial basis
#                                                                                     computation of beta^{-q} can be recycled in the whole algorithm
#            systemSolving = log(q) * n * BigFieldMul          #not sure anymore where this comes from?
#    else:                                                  here we assume normal bases
#        rightHandSide = BigFieldMul                    -q powering is O(1) assuming normal bases, only cost is for multiplication
#        systemSolving = n * SmallFieldMul * log(n)          system is circulant

#    return rightHandSide + systemSolving                 stupid answer to make sure error is detected; in fact must still be implemented






#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# looking at left-hand side column : additive algorithms
# ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------



# BTA analysis (change complexity type to WORST or AVERAGE if you want deterministic vs probabilistic complexity)
def BTA(n,d):
    TraceModF = n* log(q) * PolynomialMul(d)         # does not take into account fast modular composition
    if COMPLEXITY_TYPE == "WORST":
        h = n
    else:
        h = log(d)
    BTA = h *  (TraceModF + q* PolynomialGCD(d,d))    # uses a superlinearity argument: at lower levels you will more instances (O(k)) of smaller problems (size O(d/k)), and as the cost of each is superlinear in d we just bound all of them by the cost for the largest d
    return expand(BTA)
print "BTA costs:  ",  BTA(n,d)




# SRA analysis
precomputation = n^2 * log(q) * BigFieldMul
resultant = d^2 * BigFieldMul + PolynomialGCD(q,q)            # reduction of f coefficient-wise then Euclide algorithm
                                                              # formula supposes d>q, may become (otilde of?) dq otherwise
first_step = n * resultant
multievalGCD = q * MultiEvaluation(d/q) + d * PolynomialGCD(q,q)         # following section 4.2 in SRA paper, first term is for computing F_{0,i}^{(j-1)}(x_j) using multipoint evaluation; second term is for d gcds of degree q polynomials
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
testRoots = MultiEvaluation(d)         # find the correct roots among the O(d) remaining candidates
second_step = n*multievalGCD
questionMarksAlgo = precomputation+ first_step + testRoots + second_step
print "New algorithm costs: (note that this algorithm is probabilistic) ", questionMarksAlgo






# ARM analysis
# Original MOV version as described in Christophe's document ... not very clear
#precomputation = n^2 * log(q) * BigFieldMul # same as SRA
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
print "ARM costs (version in Christophe's July 2015 draft):  ", ARM
%typeset_mode True




# ARM analysis
# Version written by Michael in "final" paper, then modified by Luca
#precomputation = same as SRA
step3 = log(q)*PolynomialMul(d) + log(q)*BigFieldMul + d*log(q)*BigFieldMul
step23 = n*step3
if COMPLEXITY_TYPE == "WORST":
    h = n
    LofRho = n*d
else:
    h = log(d)            # use submultiplicative argument here
    LofRho = d             # use Gray code 
gcdStep = PolynomialGCD(d,d)
ARMcore = h * (LofRho + gcdStep)

ARM = precomputation + step23 + ARMcore
print "ARM costs (version in final paper's description):  ", ARM
print "\n\n"



ARM.expand()







# now looking at right-hand side column: multiplicative algorithms
# ----------------------------------------------------------------
factorization_pm1 = 1                      # improve? 
primitive_root = 1                         # improve?
n = log(q)/log(B)                          # overload variable n


# complexity of Moenck-Mignotte
# follows Christophe's draft Algorithm 9
line4 = n * log(B) * Mnot(d)








