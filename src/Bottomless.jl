module Bottomless

export @bottomless, check_shadowing

const UNION_BOTTOM = Expr(:curly, GlobalRef(Core, :Union))
const TYPE_BOTTOM = Expr(:curly, GlobalRef(Core, :Type), UNION_BOTTOM)
const ANY = GlobalRef(Core, :Any)

# ---------------------------------------------------------------------------------------------
# Parsing the method definition

struct Arg
    expr::Any
    name::Union{Symbol, Nothing}
    type::Any       # `nothing` for an untyped argument
    vararg::Bool
end

function parse_arg(a)
    a isa Symbol && return Arg(a, a, nothing, false)
    if a isa Expr
        if a.head === :macrocall    # e.g. `@nospecialize(x)`
            inner = parse_arg(a.args[end])
            return Arg(a, inner.name, inner.type, inner.vararg)
        elseif a.head === :kw       # optional argument
            inner = parse_arg(a.args[1])
            return Arg(a, inner.name, inner.type, inner.vararg)
        elseif a.head === :...
            inner = parse_arg(a.args[1])
            return Arg(a, inner.name, inner.type, true)
        elseif a.head === :(::)
            length(a.args) == 1 && return Arg(a, nothing, a.args[1], false)
            name = a.args[1] isa Symbol ? a.args[1] : nothing
            return Arg(a, name, a.args[2], false)
        elseif a.head === :tuple    # destructuring argument
            return Arg(a, nothing, nothing, false)
        end
    end
    throw(ArgumentError("`@bottomless` cannot parse the argument `$a`"))
end

struct WhereVar
    expr::Any
    name::Symbol
    lower::Any      # `nothing` if the variable has no explicit lower bound
end

function parse_where(w)
    w isa Symbol && return WhereVar(w, w, nothing)
    if w isa Expr
        if w.head === :<: && length(w.args) == 2 && w.args[1] isa Symbol
            return WhereVar(w, w.args[1], nothing)
        elseif w.head === :>: && length(w.args) == 2 && w.args[1] isa Symbol
            return WhereVar(w, w.args[1], w.args[2])
        elseif w.head === :comparison && length(w.args) == 5 && w.args[3] isa Symbol
            lower = w.args[2] === :<: ? w.args[1] : w.args[5]
            return WhereVar(w, w.args[3], lower)
        end
    end
    throw(ArgumentError("`@bottomless` cannot parse the type variable `$w`"))
end

struct Definition
    def::Any                # the whole definition, `nothing` for the declaration form
    callee::Any
    args::Vector{Arg}
    haskw::Bool
    wheres::Vector{WhereVar}
end

issignature(ex) = ex isa Expr && ex.head in (:call, :where, :(::))

function parse_definition(ex)
    if ex isa Expr && (ex.head === :function || (ex.head === :(=) && issignature(ex.args[1])))
        def, sig = ex, ex.args[1]
    elseif issignature(ex)
        def, sig = nothing, ex
    else
        throw(ArgumentError("`@bottomless` expects a method definition or a method signature, got `$ex`"))
    end
    wheres = WhereVar[]
    while sig isa Expr && sig.head === :where
        append!(wheres, map(parse_where, sig.args[2:end]))
        sig = sig.args[1]
    end
    sig isa Expr && sig.head === :(::) && (sig = sig.args[1])  # return type
    sig isa Expr && sig.head === :call ||
        throw(ArgumentError("`@bottomless` expects a method definition or a method signature, got `$ex`"))
    callee = sig.args[1]
    callee isa Symbol || (callee isa Expr && callee.head === :.) ||
        throw(ArgumentError("`@bottomless` supports named functions only, got `$callee`"))
    rest = sig.args[2:end]
    haskw = !isempty(rest) && rest[1] isa Expr && rest[1].head === :parameters
    haskw && (rest = rest[2:end])
    return Definition(def, callee, map(parse_arg, rest), haskw, wheres)
end

# ---------------------------------------------------------------------------------------------
# Detecting the type arguments that can be `Union{}`

istypehead(h) = h === :Type || h == :(Core.Type) || h == :(Base.Type) || h == GlobalRef(Core, :Type)

# Return `(true, name)` for `::Type{T}` with a type variable `T` without lower bound (`name` is `nothing`
# for `::Type{<:X}`), else `(false, nothing)`.
function bottom_variable(type, wheres::Vector{WhereVar})
    type isa Expr && type.head === :curly && length(type.args) == 2 && istypehead(type.args[1]) ||
        return false, nothing
    inner = type.args[2]
    inner isa Expr && inner.head === :<: && length(inner.args) == 1 && return true, nothing
    if inner isa Symbol
        i = findfirst(w -> w.name === inner, wheres)
        i === nothing && return false, nothing
        return wheres[i].lower === nothing, inner
    end
    return false, nothing
end

wholetype(a::Arg, var::Symbol) =
    a.type === var || (a.type isa Expr && a.type.head === :curly && a.type.args[1] === :Vararg &&
                       length(a.type.args) >= 2 && a.type.args[2] === var)

function guarded_positions(d::Definition)
    positions = Tuple{Int, Union{Symbol, Nothing}}[]
    for (k, a) in enumerate(d.args)
        a.vararg && continue
        ok, var = bottom_variable(a.type, d.wheres)
        ok || continue
        var === nothing || !any(b -> b !== a && wholetype(b, var), d.args) || continue
        push!(positions, (k, var))
    end
    return positions
end

# ---------------------------------------------------------------------------------------------
# Code generation

substitute(ex, ::Nothing) = ex
substitute(ex, var::Symbol) =
    ex === var ? UNION_BOTTOM : ex isa Expr ? Expr(ex.head, map(a -> substitute(a, var), ex.args)...) : ex

function symbols!(set::Set{Symbol}, ex)
    if ex isa Symbol
        push!(set, ex)
    elseif ex isa Expr
        foreach(a -> symbols!(set, a), ex.args)
    end
    return set
end

# The `where` entries that `types` need, without `var`, with `Union{}` in place of `var`.
function needed_wheres(types, wheres::Vector{WhereVar}, var)
    used = Set{Symbol}()
    foreach(t -> symbols!(used, t), types)
    while true
        n = length(used)
        for w in wheres
            w.name in used && w.name !== var && symbols!(used, w.expr)
        end
        length(used) == n && break
    end
    return Any[substitute(w.expr, var) for w in wheres if w.name in used && w.name !== var]
end

withwhere(ex, wheres) = isempty(wheres) ? ex : Expr(:where, ex, wheres...)

tupletype(types, wheres) = withwhere(Expr(:curly, GlobalRef(Core, :Tuple), types...), wheres)

function throwing_body(source::LineNumberNode, callee, names, slurp)
    err = Expr(:call, GlobalRef(Core, :MethodError), callee, Expr(:tuple, names..., UNION_BOTTOM, Expr(:..., slurp)))
    return Expr(:block, source, Expr(:call, GlobalRef(Core, :throw), err))
end

function guard_code(mod::Module, source::LineNumberNode, d::Definition, k::Int, var, request::Symbol,
                    explicit, hasresult::Bool, result)
    prefix = d.args[1:(k - 1)]
    names = Symbol[gensym(:prefix) for _ in prefix]
    slurp = gensym(:slurp)
    own = Any[a.type === nothing ? ANY : substitute(a.type, var) for a in prefix]
    suffix = d.args[(k + 1):end]
    suffix_exprs = Any[substitute(a.expr, var) for a in suffix]
    suffix_types = Any[let t = a.type === nothing ? ANY : substitute(a.type, var)
                           a.vararg ? Expr(:curly, GlobalRef(Core, :Vararg), t) : t
                       end for a in suffix]
    variants = Pair{Symbol, Vector{Any}}[]
    if request === :default || request === :any
        push!(variants, :any => Any[nothing for _ in prefix])
    end
    if request === :default || request === :own
        push!(variants, :own => own)
    end
    explicit_type = nothing
    if request === :explicit
        types = explicit isa Vector ? explicit : Any[explicit for _ in prefix]
        length(types) == length(prefix) || throw(ArgumentError(
            "`@bottomless`: `prefix` lists $(length(types)) types, but the argument at position $k has " *
            "$(length(prefix)) arguments before it"))
        push!(variants, :explicit => types)
        explicit_type = tupletype(types, Any[])
    end
    plan = gensym(:bottomless_plan)
    code = Expr(:block)
    push!(code.args, Expr(:(=), plan, Expr(:call, GlobalRef(Bottomless, :_plan), d.callee, mod, k,
                                           QuoteNode(request), tupletype(own, needed_wheres(own, d.wheres, var)),
                                           explicit_type, d.haskw, QuoteNode(source))))
    planfield(field) = Expr(:., plan, QuoteNode(field))
    for (variant, types) in variants
        typed = Any[t for t in types if t !== nothing]
        args = Any[t === nothing ? n : Expr(:(::), n, t) for (n, t) in zip(names, types)]
        wheres = needed_wheres(typed, d.wheres, var)
        isvariant = Expr(:call, GlobalRef(Core, :(===)), planfield(:prefix), QuoteNode(variant))
        guard = Expr(:(=), withwhere(Expr(:call, d.callee, args..., Expr(:(::), TYPE_BOTTOM), Expr(:..., slurp)), wheres),
                     throwing_body(source, d.callee, names, slurp))
        push!(code.args, Expr(:if, Expr(:&&, planfield(:positional), isvariant), Expr(:block, source, guard)))
        if d.haskw
            kwsig = Expr(:call, Expr(:., :Core, QuoteNode(:kwcall)), Expr(:(::), GlobalRef(Core, :NamedTuple)),
                         Expr(:(::), Expr(:call, GlobalRef(Core, :typeof), d.callee)), args...,
                         Expr(:(::), TYPE_BOTTOM), Expr(:..., slurp))
            kwguard = Expr(:(=), withwhere(kwsig, wheres), throwing_body(source, d.callee, names, slurp))
            push!(code.args, Expr(:if, Expr(:&&, planfield(:keyword), isvariant), Expr(:block, source, kwguard)))
        end
        if hasresult
            rwheres = needed_wheres(vcat(typed, suffix_types), d.wheres, var)
            call = Expr(:call, d.callee, args..., Expr(:(::), TYPE_BOTTOM), suffix_exprs...)
            d.haskw && insert!(call.args, 2, Expr(:parameters, Expr(:..., gensym(:kwargs))))
            sig = tupletype(Any[Expr(:call, GlobalRef(Core, :typeof), d.callee),
                                Any[t === nothing ? ANY : t for t in types]..., TYPE_BOTTOM, suffix_types...], rwheres)
            missing_result = Expr(:call, GlobalRef(Bottomless, :_lacks_method), d.callee, sig)
            resultdef = Expr(:(=), withwhere(call, rwheres), Expr(:block, source, result))
            push!(code.args, Expr(:if, Expr(:&&, isvariant, missing_result), Expr(:block, source, resultdef)))
        end
    end
    return code
end

function expand(mod::Module, source::LineNumberNode, ex, request::Symbol, explicit, hasresult::Bool, result)
    d = parse_definition(ex)
    positions = guarded_positions(d)
    isempty(positions) && throw(ArgumentError(
        "`@bottomless` found no argument `::Type{T}` in `$(d.callee)` whose `T` can be `Union{}`"))
    request === :explicit && explicit isa Vector && length(positions) > 1 && throw(ArgumentError(
        "`@bottomless`: a `prefix` tuple needs a definition with exactly one type argument that can be `Union{}`"))
    block = Expr(:block, source)
    d.def === nothing || push!(block.args, Expr(:macrocall, GlobalRef(Core, Symbol("@__doc__")), source, d.def))
    for (k, var) in positions
        append!(block.args, guard_code(mod, source, d, k, var, request, explicit, hasresult, result).args)
    end
    push!(block.args, d.callee)
    return esc(block)
end

"""
    @bottomless [prefix=…] [result=…] definition

Define `definition` and a method that throws a `MethodError` when its type argument is `Union{}`.

`Union{}` is a subtype of every type, so a method like `f(::Type{T}) where {T<:Integer}` also matches
`f(Union{})`. Two methods for unrelated types, such as `f(::Type{<:Integer})` and
`f(::Type{<:AbstractString})`, therefore overlap at `Union{}`. Julia has to consider both whenever it looks
up or inserts a method for a `Type{<:T}` argument. `f(Union{})` is ambiguous as well. A method
`f(::Type{Union{}}, slurp...)` takes precedence over all methods that match `Union{}` only through such an
overlap. Method lookup then skips these candidates. `@bottomless` adds this method next to `definition`, so
that the definition needs no second line. Base uses the same methods, e.g. for `typemax` and `round`.

# Examples
```jldoctest
julia> using Bottomless

julia> @bottomless bits(::Type{T}) where {T<:Integer} = 8sizeof(T);

julia> bits(Int16)
16

julia> try bits(Union{}) catch err; typeof(err) end
MethodError

julia> @bottomless result=false isnarrow(::Type{T}) where {T<:Integer} = sizeof(T) < 4;

julia> isnarrow(Int8), isnarrow(Union{})
(true, false)
```

# Detected arguments

`@bottomless` adds a method for each argument of `definition` for which this table says "yes". It throws
an `ArgumentError` if no argument qualifies.

| Argument | Method for `Union{}`? |
|:-------- |:--------------------- |
| `::Type{T}` with `T` from `where` and no lower bound | yes |
| `::Type{<:X}` | yes |
| `::Type{T}` with a lower bound, as in `where {T >: Int}` | no, `T` cannot be `Union{}` |
| `::Type{Int}` or another fixed type | no |
| plain `::Type` | no, the method takes every type on purpose |
| `T` is also the type of another argument, as in `f(x::T, ::Type{T})` | no, no value has type `Union{}`, so the call cannot happen |
| `T` also occurs inside another argument type, as in `f(v::Vector{T}, ::Type{T})` | yes, with `Union{}` in place of `T` |
| a type argument in a vararg, as in `f(::Type{T}...)` | no |

# Prefix

The arguments before the type argument form the prefix. A method with a narrow prefix only covers calls with
matching arguments there. A method with a wide prefix also shadows methods that take an arbitrary value at
the type argument's position, such as `peek(s::Iterators.Stateful, sentinel)` in Base.

- If the function belongs to the package that calls `@bottomless`, the prefix is untyped. The new method
  then covers the methods that other packages add. For code in `Main`, each module directly below `Main`
  counts as a package.
- Otherwise the prefix types are those of `definition`. If they contain a type of the calling package, the
  new method is no type piracy.

`prefix=own` uses the types of `definition`, `prefix=T` uses `T` for every prefix argument, and
`prefix=(T1, T2)` lists the type of each prefix argument. `prefix=Any` is untyped.

# Existing methods

`@bottomless` checks the existing methods when the definition runs:

- It adds nothing if an existing `Type{Union{}}` method covers the prefix. Several annotated methods of one
  function therefore share a method, wherever they are defined.
- It throws an `ArgumentError` if an existing `Type{Union{}}` method only overlaps the prefix, because calls
  in the overlap would be ambiguous. Choose a prefix with `prefix=` or write the methods by hand.
- It adds nothing and logs a warning if the method would be type piracy: the function belongs to another
  package and the prefix contains no type of the calling package. Add the method in the package that owns
  the function.

# Keyword arguments

If `definition` has keyword arguments, `@bottomless` also adds a `Core.kwcall` method. `f(Union{}; k = 1)`
then throws the same `MethodError` as `f(Union{})`.

# Results

`result=value` also defines a method with the arguments of `definition`, with `Type{Union{}}` at the type
argument, that returns `value`. Calls with extra arguments still throw. Use this only if `Union{}` has a
meaningful result, e.g. `false` for a predicate on types.

# Declaration form

Without a method body (`@bottomless f(::Type{<:AbstractFloat})`), `@bottomless` only adds the methods for
`Union{}`. Use this for a function whose own methods take fixed types, such as `f(::Type{Float64})`, which
other packages extend with `Type{<:T}` methods.

Use `@bottomless` at the top level of a module. Test the result with [`check_shadowing`](@ref).
"""
macro bottomless(args...)
    isempty(args) && throw(ArgumentError("`@bottomless` needs a method definition"))
    request, explicit, hasresult, result = :default, nothing, false, nothing
    for option in args[1:(end - 1)]
        option isa Expr && option.head === :(=) && length(option.args) == 2 ||
            throw(ArgumentError("`@bottomless` expects options `prefix=…` and `result=…`, got `$option`"))
        key, value = option.args
        if key === :prefix
            if value === :own
                request = :own
            elseif value === :Any
                request = :any
            elseif value isa Expr && value.head === :tuple
                request, explicit = :explicit, Any[value.args...]
            else
                request, explicit = :explicit, value
            end
        elseif key === :result
            hasresult, result = true, value
        else
            throw(ArgumentError("`@bottomless` has no option `$key`"))
        end
    end
    return expand(__module__, __source__, args[end], request, explicit, hasresult, result)
end

# ---------------------------------------------------------------------------------------------
# Decisions at execution time

# The package of `m`: the root module, or the topmost module below `Main` for code that runs in `Main`.
function package_of(m::Module)
    while true
        p = parentmodule(m)
        (p === m || p === Main) && return m
        m = p
    end
end

owns(mod::Module, @nospecialize(f)) = package_of(parentmodule(f)) === package_of(mod)

function owns_type(mod::Module, @nospecialize(t))
    t isa TypeVar && return owns_type(mod, t.ub)
    t isa UnionAll && return owns_type(mod, Base.unwrap_unionall(t))
    t isa Union && return owns_type(mod, t.a) || owns_type(mod, t.b)
    if Base.isvarargtype(t)
        return isdefined(t, :T) && owns_type(mod, t.T)
    end
    t isa Type && hasproperty(t, :name) && hasproperty(t, :parameters) || return false
    package_of(t.name.module) === package_of(mod) && return true
    return any(p -> owns_type(mod, p), t.parameters)
end

# The positional or keyword method for `Union{}` at `position` that covers the prefix `prefix`, else `nothing`.
function covering(@nospecialize(f), position::Int, @nospecialize(prefix::Type), keyword::Bool, source::LineNumberNode)
    candidates = keyword ? methods(Core.kwcall, Tuple{NamedTuple, typeof(f), Vararg{Any}}) : methods(f)
    lead = keyword ? 2 : 0
    for m in candidates
        ps = Base.unwrap_unionall(m.sig).parameters
        n = length(ps)
        n == lead + position + 2 && Base.isvarargtype(ps[n]) && ps[n - 1] == Type{Union{}} || continue
        keyword && ps[3] != typeof(f) && continue
        existing = Base.rewrap_unionall(Tuple{Any[ps[j] for j in (lead + 2):(n - 2)]...}, m.sig)
        prefix <: existing && return m
        if !(existing <: prefix) && typeintersect(prefix, existing) !== Union{}
            throw(ArgumentError(
                "`@bottomless` at $(source.file):$(source.line): the method for `Union{}` with prefix " *
                "`$prefix` would overlap the existing method `$m` only partially, which makes calls in the " *
                "overlap ambiguous. Choose a prefix with `prefix=` that contains the existing one or lies " *
                "within it, or write the methods by hand."))
        end
    end
    return nothing
end

function _plan(@nospecialize(f), mod::Module, position::Int, request::Symbol, @nospecialize(own::Type),
               @nospecialize(explicit), keyword::Bool, source::LineNumberNode)
    owner = owns(mod, f)
    prefix = request === :default ? (owner ? :any : :own) : request
    P = prefix === :any ? NTuple{position - 1, Any} : prefix === :own ? own : explicit::Type
    positional = covering(f, position, P, false, source) === nothing
    kw = keyword && covering(f, position, P, true, source) === nothing
    if !owner && !owns_type(mod, P)
        (positional || kw) && @warn(
            "`@bottomless`: `$f` has no method for `Union{}` at argument $position that covers the prefix " *
            "`$P`. Defining it here would be type piracy, so add it in the package that owns `$f`.",
            _file = String(source.file), _line = source.line)
        return (prefix = :none, positional = false, keyword = false)
    end
    return (prefix = prefix, positional = positional, keyword = kw)
end

_lacks_method(@nospecialize(f), @nospecialize(sig::Type)) = !any(m -> m.sig == sig, methods(f))

# ---------------------------------------------------------------------------------------------
# Auditing

function guard_position(m::Method)
    ps = Base.unwrap_unionall(m.sig).parameters
    n = length(ps)
    return n >= 3 && Base.isvarargtype(ps[n]) && ps[n - 1] == Type{Union{}} ? n - 1 : nothing
end

function within(m::Module, mod::Module)
    while true
        m === mod && return true
        p = parentmodule(m)
        p === m && return false
        m = p
    end
end

function all_modules()
    found = Base.IdSet{Module}()
    pending = Module[Core, Base, Main, Base.loaded_modules_array()...]
    while !isempty(pending)
        M = pop!(pending)
        M in found && continue
        push!(found, M)
        for name in names(M; all = true)
            isdefined(M, name) || continue
            v = getglobal(M, name)
            v isa Module && parentmodule(v) === M && v !== M && push!(pending, v)
        end
    end
    return found
end

function foreach_method(visit, mod::Module)
    if isdefined(Core, :methodtable)
        Base.visit(m -> m isa Method && visit(m), Core.methodtable)
    else
        seen = Base.IdSet{Any}()
        for M in all_modules(), name in names(M; all = true)
            isdefined(M, name) && !Base.isdeprecated(M, name) || continue
            v = getglobal(M, name)
            v isa Function && !(v in seen) || continue
            push!(seen, v)
            foreach(visit, methods(v))
        end
    end
end

# The type of argument `i` (signature index) of `ps`, or `nothing` if the method takes fewer arguments.
function argument_type(ps, i::Int)
    for (j, p) in enumerate(ps)
        Base.isvarargtype(p) && return isdefined(p, :T) ? p.T : Any
        j == i && return p
    end
    return nothing
end

"""
    check_shadowing(mod::Module)::Vector{@NamedTuple{guard::Method, shadowed::Method}}

Return the methods that a method for `Union{}` of `mod` shadows although they take a value at its position.

A method like `f(x, ::Type{Union{}}, slurp...)` takes precedence over every method of `f` that matches its
call shape. That is intended for methods with a type argument there, such as `f(x, ::Type{T}) where T`.
It is a bug for a method that takes an arbitrary value at that position, such as a sentinel or a default
value. Each returned pair holds such a method (`shadowed`) and the method for `Union{}` (`guard`) that
covers its calls with the value `Union{}`. Restrict the prefix of the guard, e.g. with `prefix=` in
[`@bottomless`](@ref).

`check_shadowing` checks the methods of the shape `f(…, ::Type{Union{}}, slurp...)` defined in `mod` or
its submodules, whether `@bottomless` or a hand-written definition created them. Call it in the tests,
after all methods are defined: a method defined later is not visible when `@bottomless` runs.

# Examples
```jldoctest
julia> using Bottomless

julia> @bottomless probe(s::IO, ::Type{T}) where {T} = read(s, T);

julia> probe(v::Vector, sentinel) = isempty(v) ? sentinel : first(v);

julia> count(r -> r.guard.name === :probe, check_shadowing(@__MODULE__))
1

julia> @bottomless prefix=IO probe2(s::IO, ::Type{T}) where {T} = read(s, T);

julia> probe2(v::Vector, sentinel) = isempty(v) ? sentinel : first(v);

julia> count(r -> r.guard.name === :probe2, check_shadowing(@__MODULE__))
0
```
"""
function check_shadowing(mod::Module)
    guards = Method[]
    foreach_method(mod) do m
        within(m.module, mod) && guard_position(m) !== nothing && push!(guards, m)
    end
    result = @NamedTuple{guard::Method, shadowed::Method}[]
    for g in guards
        fT = Base.unwrap_unionall(g.sig).parameters[1]
        fT isa DataType && isdefined(fT, :instance) || continue
        i = guard_position(g)::Int
        gps = Base.unwrap_unionall(g.sig).parameters
        gprefix = Base.rewrap_unionall(Tuple{Any[gps[j] for j in 2:(i - 1)]...}, g.sig)
        for m in methods(fT.instance)
            m === g && continue
            ps = Base.unwrap_unionall(m.sig).parameters
            any(q -> q == Type{Union{}}, ps) && continue        # another method for `Union{}`
            p = argument_type(ps, i)
            p === nothing && continue
            value = Base.rewrap_unionall(p, m.sig)
            value <: Type && continue                          # a type argument: shadowing is intended
            typeintersect(value, Type{Union{}}) === Union{} && continue
            mprefix = Base.rewrap_unionall(Tuple{Any[argument_type(ps, j) for j in 2:(i - 1)]...}, m.sig)
            typeintersect(gprefix, mprefix) === Union{} && continue
            push!(result, (guard = g, shadowed = m))
        end
    end
    return result
end

end # module Bottomless
