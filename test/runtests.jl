using Test
using Aqua
using Bottomless

# A new module directly below `Main`, which `@bottomless` treats as a package of its own.
function fresh()
    M = Core.eval(Main, :(module $(gensym(:Package)) end))
    Core.eval(M, :(using Bottomless))
    return M
end

guard_sigs(f) = [m.sig for m in methods(f) if Bottomless.guard_position(m) !== nothing]

innermost(err) = err isa LoadError ? innermost(err.error) : err

function expansion_error(args...)
    call = Expr(:macrocall, GlobalRef(Bottomless, Symbol("@bottomless")), LineNumberNode(@__LINE__, @__FILE__), args...)
    try
        macroexpand(Main, call)
    catch err
        return innermost(err)
    end
    return nothing
end

function execution_error(M::Module, ex)
    try
        Core.eval(M, ex)
    catch err
        return innermost(err)
    end
    return nothing
end

@testset "Bottomless" begin

@testset "Aqua" begin
    Aqua.test_all(Bottomless)
end

@testset "doctests" begin
    if isempty(VERSION.prerelease)
        @eval using Documenter
        Documenter.doctest(Bottomless; manual = false)
    end
end

@testset "detected arguments" begin
    M = fresh()
    Core.eval(M, quote
        @bottomless a(::Type{T}) where {T<:Integer} = 1
        @bottomless b(::Type{<:Integer}) = 2
        @bottomless c(v::Vector{T}, ::Type{T}) where {T} = 3
        @bottomless prefix=own d(v::Vector{T}, ::Type{T}) where {T} = 4
        @bottomless e(::Type{S}, ::Type{T}) where {S<:Real, T<:Integer} = 5
        @bottomless g(::Type{T}, ::Type{Int}) where {T<:Real} = 6
    end)
    @test M.a(Int) == 1
    @test guard_sigs(M.a) == [Tuple{typeof(M.a), Type{Union{}}, Vararg{Any}}]
    @test_throws MethodError(M.a, (Union{},)) M.a(Union{})
    @test_throws MethodError(M.a, (Union{}, 1)) M.a(Union{}, 1)
    @test guard_sigs(M.b) == [Tuple{typeof(M.b), Type{Union{}}, Vararg{Any}}]
    @test guard_sigs(M.c) == [Tuple{typeof(M.c), Any, Type{Union{}}, Vararg{Any}}]
    @test guard_sigs(M.d) == [Tuple{typeof(M.d), Vector{Union{}}, Type{Union{}}, Vararg{Any}}]
    @test_throws MethodError(M.d, (Union{}[], Union{})) M.d(Union{}[], Union{})
    @test length(guard_sigs(M.e)) == 2
    @test_throws MethodError(M.e, (Union{}, Int)) M.e(Union{}, Int)
    @test_throws MethodError(M.e, (Float64, Union{})) M.e(Float64, Union{})
    @test_throws MethodError M.e(Union{}, Union{})
    @test guard_sigs(M.g) == [Tuple{typeof(M.g), Type{Union{}}, Vararg{Any}}]
    @test isempty(Test.detect_ambiguities(M))

    for def in (:(f(::Type{T}) where {T >: Int} = 1),
                :(f(::Type{T}) where {Int <: T <: Real} = 1),
                :(f(::Type{Int}) = 1),
                :(f(::Type) = 1),
                :(f(x::T, ::Type{T}) where {T} = 1),
                :(f(::Type{T}...) where {T} = 1),
                :(f(x) = 1))
        @test expansion_error(def) isa ArgumentError
    end
end

@testset "ownership and prefix" begin
    Owner = fresh()
    Core.eval(Owner, quote
        @bottomless r(x::Integer, ::Type{T}) where {T<:Integer} = 1
        @bottomless r(x::AbstractChar, ::Type{T}) where {T<:Number} = 2
        function af end
        af(::Type{Int}) = 1
        function af2 end
        af2(::Type{Int}) = 1
    end)
    # the owner leaves the prefix untyped, so both methods share one guard
    @test guard_sigs(Owner.r) == [Tuple{typeof(Owner.r), Any, Type{Union{}}, Vararg{Any}}]
    @test_throws MethodError(Owner.r, ('a', Union{})) Owner.r('a', Union{})

    Extender = fresh()
    Core.eval(Extender, quote
        struct Wrapped end
        @bottomless $Owner.af(x::Wrapped, ::Type{T}) where {T<:Integer} = 2
        @bottomless $Owner.r(x::Wrapped, ::Type{T}) where {T<:Integer} = 3
    end)
    @test guard_sigs(Owner.af) == [Tuple{typeof(Owner.af), Extender.Wrapped, Type{Union{}}, Vararg{Any}}]
    @test length(guard_sigs(Owner.r)) == 1   # covered by the owner's guard

    Pirate = fresh()
    @test_logs (:warn, r"type piracy") Core.eval(Pirate, :(@bottomless $Owner.af2(::Type{T}) where {T<:Integer} = 3))
    @test isempty(guard_sigs(Owner.af2))
end

@testset "prefix option" begin
    M = fresh()
    Core.eval(M, quote
        @bottomless prefix=IO pk(s::IO, ::Type{T}) where {T} = read(s, T)
        pk(v::Vector, sentinel) = isempty(v) ? sentinel : first(v)
        @bottomless prefix=(Integer, Real) q(x::Int, y::Float64, ::Type{T}) where {T} = 1
        @bottomless prefix=Any z(x::Int, ::Type{T}) where {T} = 1
        @bottomless prefix=own w(x::Int, ::Type{T}) where {T} = 1
    end)
    @test guard_sigs(M.pk) == [Tuple{typeof(M.pk), IO, Type{Union{}}, Vararg{Any}}]
    @test M.pk(Int[], Union{}) === Union{}
    @test M.pk([1], Union{}) === 1
    io = IOBuffer()
    @test_throws MethodError(M.pk, (io, Union{})) M.pk(io, Union{})
    @test guard_sigs(M.q) == [Tuple{typeof(M.q), Integer, Real, Type{Union{}}, Vararg{Any}}]
    @test guard_sigs(M.z) == [Tuple{typeof(M.z), Any, Type{Union{}}, Vararg{Any}}]
    @test guard_sigs(M.w) == [Tuple{typeof(M.w), Int, Type{Union{}}, Vararg{Any}}]

    @test expansion_error(:(prefix = (Int,)), :(f(::Type{S}, ::Type{T}) where {S, T} = 1)) isa ArgumentError
    @test expansion_error(:(prefix = (Int, Int)), :(f(x, ::Type{T}) where {T} = 1)) isa ArgumentError
    @test expansion_error(:(unknown = 1), :(f(::Type{T}) where {T} = 1)) isa ArgumentError
    @test expansion_error(:prefix, :(f(::Type{T}) where {T} = 1)) isa ArgumentError
    @test expansion_error() isa ArgumentError
end

@testset "existing methods" begin
    M = fresh()
    Core.eval(M, quote
        begin
            @bottomless k(::Type{T}) where {T<:Integer} = 1
            @bottomless k(::Type{T}) where {T<:AbstractString} = 2
        end
    end)
    @test length(guard_sigs(M.k)) == 1
    @test_throws MethodError(M.k, (Union{},)) M.k(Union{})
    Core.eval(M, :(@bottomless k(::Type{<:Integer})))
    @test length(guard_sigs(M.k)) == 1

    Core.eval(M, :(@bottomless prefix=Union{Int, String} po(x, ::Type{T}) where {T} = 1))
    err = execution_error(M, :(@bottomless prefix=Union{Int, Float64} po(x::Float64, ::Type{T}) where {T<:Real} = 2))
    @test err isa ArgumentError && occursin("partially", err.msg)

    Core.eval(M, :(@bottomless prefix=Int wide(x, ::Type{T}) where {T} = 1))
    Core.eval(M, :(@bottomless prefix=Integer wide(x::Integer, ::Type{T}) where {T<:Real} = 2))
    @test length(guard_sigs(M.wide)) == 2
    @test_throws MethodError(M.wide, (1, Union{})) M.wide(1, Union{})
    @test isempty(Test.detect_ambiguities(M))
end

@testset "keyword arguments" begin
    M = fresh()
    Core.eval(M, :(@bottomless h(x::Int, ::Type{T}; base = 2) where {T<:Real} = base))
    @test M.h(1, Int; base = 3) == 3
    @test_throws MethodError(M.h, (1, Union{})) M.h(1, Union{})
    @test_throws MethodError(M.h, (1, Union{})) M.h(1, Union{}; base = 3)
end

@testset "result option" begin
    M = fresh()
    Core.eval(M, quote
        @bottomless result=false isnarrow(::Type{T}) where {T<:Integer} = sizeof(T) < 4
        @bottomless result=false valid(::Type{T}, c::Unsigned) where {T<:AbstractChar} = true
        @bottomless result=false valid(::Type{T}, c::AbstractChar) where {T<:AbstractChar} = true
        @bottomless result=0 counted(::Type{T}; k = 1) where {T<:Real} = k
    end)
    @test M.isnarrow(Int8)
    @test M.isnarrow(Union{}) === false
    @test_throws MethodError(M.isnarrow, (Union{}, 1)) M.isnarrow(Union{}, 1)
    @test M.valid(Union{}, 0x41) === false
    @test M.valid(Union{}, 'a') === false
    @test_throws MethodError(M.valid, (Union{}, "a")) M.valid(Union{}, "a")
    @test M.counted(Union{}; k = 5) === 0
    Core.eval(M, :(@bottomless result=false isnarrow(::Type{T}) where {T<:Integer}))
    @test length(methods(M.isnarrow)) == 3
end

@testset "declaration form" begin
    M = fresh()
    Core.eval(M, quote
        ep(::Type{Float64}) = 1.0
        @bottomless ep(::Type{<:AbstractFloat})
    end)
    @test M.ep(Float64) == 1.0
    @test_throws MethodError(M.ep, (Union{},)) M.ep(Union{})
    @test length(methods(M.ep)) == 2
end

@testset "docstrings" begin
    M = fresh()
    Core.eval(M, quote
        "Return the number of bits."
        @bottomless bits(::Type{T}) where {T<:Integer} = 8sizeof(T)
    end)
    @test haskey(Base.Docs.meta(M), Base.Docs.Binding(M, :bits))
end

@testset "unsupported definitions" begin
    @test expansion_error(:((::Vector)(::Type{T}) where {T} = 1)) isa ArgumentError
    @test expansion_error(:(function f end)) isa ArgumentError
    @test expansion_error(1) isa ArgumentError
end

@testset "check_shadowing" begin
    M = fresh()
    Core.eval(M, quote
        @bottomless pk(s::IO, ::Type{T}) where {T} = read(s, T)
        pk(v::Vector, sentinel) = isempty(v) ? sentinel : first(v)
        @bottomless e(::Type{S}, ::Type{T}) where {S<:Real, T<:Integer} = 1
        @bottomless result=false isnarrow(::Type{T}) where {T<:Integer} = true
    end)
    found = check_shadowing(M)
    @test length(found) == 1
    @test only(found).guard.sig == Tuple{typeof(M.pk), Any, Type{Union{}}, Vararg{Any}}
    @test only(found).shadowed.sig == Tuple{typeof(M.pk), Vector, Any}
    @test isempty(check_shadowing(fresh()))
end

@testset "precompiled package" begin
    mktempdir() do dir
        src = joinpath(dir, "BottomlessUser", "src")
        mkpath(src)
        write(joinpath(src, "BottomlessUser.jl"), """
            module BottomlessUser
            using Bottomless
            struct Wrapped end
            begin
                @bottomless width(::Type{T}) where {T<:Integer} = 8sizeof(T)
                @bottomless width(::Type{T}) where {T<:AbstractFloat} = 8sizeof(T)
            end
            @bottomless scaled(x::Wrapped, ::Type{T}; by = 1) where {T<:Real} = T(by)
            @bottomless Base.rem(x::Wrapped, ::Type{T}) where {T<:Integer} = zero(T)
            end
            """)
        code = """
            using BottomlessUser: width, scaled, Wrapped
            width(Int8) == 8 || error("width")
            for (f, args) in ((width, (Union{},)), (scaled, (Wrapped(), Union{})), (rem, (Wrapped(), Union{})))
                try
                    f(args...)
                    error("no MethodError")
                catch err
                    err isa MethodError || rethrow()
                end
            end
            try
                scaled(Wrapped(), Union{}; by = 2)
                error("no MethodError")
            catch err
                err isa MethodError || rethrow()
            end
            count(m -> any(==(Type{Union{}}), Base.unwrap_unionall(m.sig).parameters), methods(width)) == 1 ||
                error("guards")
            print("ok")
            """
        separator = Sys.iswindows() ? ";" : ":"
        env = copy(ENV)
        env["JULIA_LOAD_PATH"] = join([dir, pkgdir(Bottomless), "@stdlib"], separator)
        env["JULIA_DEPOT_PATH"] = mktempdir() * separator
        out, err = IOBuffer(), IOBuffer()
        cmd = setenv(`$(Base.julia_cmd()) --startup-file=no -e $code`, env)
        ok = success(pipeline(cmd; stdout = out, stderr = err))
        errors = String(take!(err))
        @test ok
        @test String(take!(out)) == "ok"
        @test !occursin("overwritten", errors)
        @test !occursin("WARNING", errors)
        ok || println(errors)
    end
end

end
