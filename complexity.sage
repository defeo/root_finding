# symbolic variables
%var q,d,n

# STANDARD OR FAST ARITHMETIC
ARITHMETIC = "FAST"      # Options are "FAST" and "STANDARD"

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