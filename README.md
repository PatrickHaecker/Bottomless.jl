# Bottomless.jl

`Union{}` is a subtype of every type, so a method `f(::Type{T}) where {T<:Integer}` also matches
`f(Union{})`. Two methods for unrelated types, such as `f(::Type{<:Integer})` and `f(::Type{<:AbstractString})`,
therefore overlap at `Union{}`. Julia has to consider both whenever it looks up or inserts a method for a
`Type{<:T}` argument, and `f(Union{})` is ambiguous.

A method `f(::Type{Union{}}, slurp...)` takes precedence over all methods that match `Union{}` only through
such an overlap, so method lookup skips them ([JuliaLang/julia#49470](https://github.com/JuliaLang/julia/pull/49470)).
Base defines these methods for many functions, e.g. `typemax`, `round` and `convert`.
`@bottomless` adds them to your methods without an extra line:

```julia
using Bottomless

@bottomless bits(::Type{T}) where {T<:Integer} = 8sizeof(T)

bits(Int16)     # 16
bits(Union{})   # MethodError
```

`@bottomless` finds the type arguments that can be `Union{}`, chooses the arguments before them so that the new
method neither shadows unrelated methods nor commits type piracy, and skips methods that already exist.
See the docstring of `@bottomless` for the rules and options.

Test your package with `check_shadowing`. It reports methods that take an arbitrary value, such as a sentinel,
at the position of a `Type{Union{}}` method and are therefore shadowed by it:

```julia
using Bottomless, Test

@test isempty(check_shadowing(MyPackage))
```

## Background

- [JuliaLang/julia#49470](https://github.com/JuliaLang/julia/pull/49470) introduced the precedence of
  `Type{Union{}}` methods.
- [JuliaLang/julia#63338](https://github.com/JuliaLang/julia/pull/63338) made these methods throw a `MethodError`
  for arguments they only take for method lookup.
- [JuliaLang/julia#62265](https://github.com/JuliaLang/julia/pull/62265) proposes type variables that exclude
  `Union{}` in the type system. `@bottomless` covers the common case until then.
