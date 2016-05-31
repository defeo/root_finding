module RootFind
using Nemo

#export 

include("tree.jl")


"""
Compute the γ_i,j = L_i(v_j) from a basis.
"""
function Γ{T<:Nemo.FiniteFieldElem}(basis::Array{T,1})
    K = parent(basis[1])
    p = characteristic(K)
    n = degree(K)
    @assert n == length(basis)
    
    # Uses the plain recursive definition of L_i.
    # Complexity is evidently O(n² log p) mulitpilication in K.
    Γ = zeros(K, n, n)
    Γ[1,:] = basis
    for i in 2:n
        α = Γ[i-1, i-1]^(p-1)
        for (j, v) in enumerate(basis)
            γ = Γ[i-1, j]
            Γ[i, j] = γ^p - α * γ
        end
    end
    Γ
end

"""
Computes the resultant

    Res_x(f(x), y - x^p + β^(p-1)x)
"""
function resultant{T<:Nemo.FiniteFieldElem}(f::PolyElem{T}, β::T)
    K = base_ring(f)
#    z = gen(K)
    n = degree(K)
#    P = parent(f)
#    X = gen(P)
    p = characteristic(K)
    d = degree(f)
    assert(parent(β) == K) # ??
    assert(d < order(K) // p)
    α = β^(p-1)

    points = _avoid_b(β, d+1)
    projs = [pt^p - α*pt for pt in points]
    
    evals = multieval(f, β, points, projs)

    return (-1)^(d % 2) * ntl_interpolate(projs, evals)
end

end

