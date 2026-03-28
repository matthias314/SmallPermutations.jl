module SmallPermutations

export SmallPermutation

import Base: copy, convert, ==, ^, *, one, inv

using AbstractPermutations: AbstractPermutation
import AbstractPermutations: degree, inttype, __unsafe_image, __images_vector, CycleDecomposition, __isodd

using SmallCollections: FixedVector, MutableFixedVector, SmallVector, resize
using SmallCollections: ntuple  # better for vectorizing than ntuple from Base

const U = UInt8

struct SmallPermutation{N} <: AbstractPermutation
    v::FixedVector{N,U}
    deg::Int
    global _SmallPermutation(v::FixedVector{N,U}, deg::Int) where N = new{N}(v, deg)
end

@inline function _SmallPermutation(v::FixedVector{N,U}) where N
    i = findlast(map(!=, v, FixedVector{N,U}(1:N)))
    deg = i === nothing ? 0 : i
    _SmallPermutation(v, deg)
end

@inline function SmallPermutation{N}(v::AbstractVector{<:Integer}; check::Bool = true) where N
    @inline
    if check
        a, b = extrema(v)
        (a, b) == (1, length(v)) || error("not a permutation")
        b <= N <= typemax(U) || error("permutation too big")
    end
    w = MutableFixedVector{N,U}(1:N)
    for i in eachindex(v)
        @inbounds w[i] = v[i] % U
    end
    if check
        allunique(w) || error("not a permutation")
    end
    _SmallPermutation(FixedVector(w))
end

degree(p::SmallPermutation) = p.deg

__images_vector(p::SmallPermutation) = @inbounds resize(SmallVector(p.v), p.deg)

inttype(::Type{<:SmallPermutation}) = U

copy(p::SmallPermutation) = p

function convert(::Type{SmallPermutation{N}}, p::SmallPermutation{M}) where {N,M}
    N <= typemax(U) || error("permutation too big")
    M <= N || p.deg <= N || error("permutation too big")
    _SmallPermutation(unsafe_resize(p.v, Val(N)), p.deg)
end

__unsafe_image(n::T, p::SmallPermutation) where T <: Integer = @inbounds(p.v[n]) % T

function ^(n::T, p::SmallPermutation{N}) where {T <: Integer, N}
    # 1 <= n <= N ? __unsafe_image(n, p) : n
    (n-1) % UInt < UInt(N) ? __unsafe_image(n, p) : n
end

function one(::Type{SmallPermutation{N}}) where N
    N <= typemax(U) || error("permutation too big")
    _SmallPermutation(FixedVector{N,U}(1:N), 0)
end

function unsafe_resize(v::FixedVector{N,U}, ::Val{M}) where {N,M}
    FixedVector(ntuple(i -> i <= N ? v[i] : U(i), Val(M)))
end

function ==(p::SmallPermutation{L}, q::SmallPermutation{M}) where {L,M}
    N = max(L, M)
    unsafe_resize(p.v, Val(N)) == unsafe_resize(q.v, Val(N))
end

@inline function *(p::SmallPermutation{L}, q::SmallPermutation{M}) where {L,M}
    N = max(L, M)
    pv = unsafe_resize(p.v, Val(N))
    qv = unsafe_resize(q.v, Val(N))
    @inbounds _SmallPermutation(qv[pv])
end

*(p::SmallPermutation, q::SmallPermutation, rs::Vararg{SmallPermutation,M}) where M = *(p*q, rs...)

function inv(p::SmallPermutation{N}) where N
    w = MutableFixedVector{N,U}(1:N)
    for i in 1:degree(p)
        @inbounds w[p.v[i]] = i % U
    end
    _SmallPermutation(FixedVector(w), degree(p))
end

^(p::SmallPermutation, q::SmallPermutation) = inv(q) * p * q

function ^(σ::SmallPermutation, n::Integer)
    if n == 0 || isone(σ)
        return one(σ)
    elseif n == -1
        return inv(σ)
    elseif n == 1
        return copy(σ)
    elseif n < 0
        return inv(σ)^-n
    elseif n == 2
        return σ * σ
    elseif n == 3
        return σ * σ * σ
    elseif n == 4
        σ² = σ * σ
        return σ² * σ²
    elseif n == 5
        σ² = σ * σ
        return σ² * σ² * σ
    elseif n == 6
        σ³ = σ * σ * σ
        return σ³ * σ³
    elseif n == 7
        σ³ = σ * σ * σ
        return σ³ * σ³ * σ
    elseif n == 8
        σ² = σ * σ
        σ⁴ = σ² * σ²
        return σ⁴ * σ⁴
    else
        Base.power_by_squaring(σ, n)
    end
end

for N in (16, 32, 64, 128)
    m = Symbol("smallperm", N, "_str")
    @eval export $(Symbol('@', m))
    @eval macro $m(str)
        Expr(:call, parse, SmallPermutation{$N}, str)
    end
end

# this part needs a modified version of AbstractPermutations

using SmallCollections: MutableSmallVector, SmallBitSet, pop

function CycleDecomposition(p::SmallPermutation{N}) where N
    cycles = zero(MutableFixedVector{N,U})
    cycles_ptrs = zero(MutableFixedVector{N,U})
    s = @inbounds SmallBitSet(Base.OneTo(degree(p)))
    a = b = 0
    @inbounds while !isempty(s)
        j = i = first(s) % U
        cycles_ptrs[b += 1] = a+1
        while true
            s = first(pop(s, j))  # or unsafe_delete
            cycles[a += 1] = j
            j = p.v[j]
            j == i && break
        end
    end
    @inbounds cycles_ptrs[b+1] = (degree(p)+1) % U
    CycleDecomposition(SmallVector(cycles, a), SmallVector(cycles_ptrs, b+1))
end

# end of this part

using SmallCollections: SmallBitSet, support, bits, unsafe_lshr

function __isodd(p::SmallPermutation)
    s = 0
    for i in 1:p.deg-1
        t = @inbounds support(<(p.v[i]), p.v)
        s += count_ones(unsafe_lshr(bits(t), i))
    end
    isodd(s)
end

end # module
