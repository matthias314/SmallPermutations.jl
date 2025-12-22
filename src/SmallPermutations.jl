module SmallPermutations

export SmallPermutation

import Base:
    copy, convert, ==, ^, *, one, inv, size, getindex

using AbstractPermutations:
    AbstractPermutation, AbstractCycleDecomposition
import AbstractPermutations:
    degree, inttype, __unsafe_image, __images_vector, __isodd, cycles

using SmallCollections:
    FixedVector, MutableFixedVector, SmallVector, resize,
    smallbitsettype, support, bits, unsafe_lshr, unsafe_delete, uinttype
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

function __isodd(p::SmallPermutation)
    s = 0
    for i in 1:p.deg-1
        t = @inbounds support(<(p.v[i]), p.v)
        s += count_ones(unsafe_lshr(bits(t), i))
    end
    isodd(s)
end

# cycle decomposition

struct SmallCycleDecomposition{N,T<:Integer} <: AbstractCycleDecomposition{T,SubArray{T,1,SmallVector{N,T},Tuple{UnitRange{Int64}},true}}
    cycles::SmallVector{N,T} # cycles, concatenated
    cycles_ptrs::SmallVector{N,T} # pointers to the starts of the cycles
end

size(cd::SmallCycleDecomposition) = (length(cd.cycles_ptrs)-1,)

degree(cd::SmallCycleDecomposition) = length(cd.cycles)

using Base: @propagate_inbounds

@inline function getindex(cd::SmallCycleDecomposition, i::Int)
    @boundscheck checkbounds(cd, i)
    @inbounds ii = cd.cycles_ptrs[i]:cd.cycles_ptrs[i+1]-1
    @inbounds cd.cycles[ii]
    @inbounds view(cd.cycles, ii)
end

function cycles(p::SmallPermutation{N}) where N
    cycles = zero(MutableFixedVector{N,U})
    cycles_ptrs = zero(MutableFixedVector{N,U})
    S = smallbitsettype(Val(N))
    s = @inbounds S(Base.OneTo(degree(p)))
    a = b = U(0)
    @inbounds while !isempty(s)
        j = i = first(s) % U
        cycles_ptrs[b += U(1)] = a + U(1)
        while true
            s = unsafe_delete(s, j)
            cycles[a += U(1)] = j
            j = p.v[j]
            j == i && break
        end
    end
    @inbounds cycles_ptrs[b + U(1)] = (degree(p)+1) % U
    SmallCycleDecomposition(SmallVector(cycles, a), SmallVector(cycles_ptrs, b + U(1)))
end

end # module
