using Hecke

export FunFldDiff

export differential, basis_of_differentials

################################################################################
#
#  Constructors
#
################################################################################

mutable struct FunFldDiff
  function_field::AbstractAlgebra.Generic.FunctionField
  f::Generic.FunctionFieldElem
  dx::String

  function FunFldDiff(f::Generic.FunctionFieldElem; dx::String = "x")
    r = new()
    
    r.function_field = parent(f)
    r.dx = dx
    r.f = f
    
    return r
  end

end

@doc Markdown.doc"""
    differential(f::Generic.FunctionFieldElem) -> Differential

Return the differential df.
"""
function differential(f::Generic.FunctionFieldElem)
  F = parent(f)
  y = gen(F)
  x = gen(base_ring(F))
    
  fnum = to_bivariate(numerator(f))
  fdenom = to_bivariate(denominator(f))
  
  df = derivative(fnum//fdenom, 1)
  df = numerator(df)(x, y)//denominator(df)(x, y)
  
  return FunFldDiff(df; dx = string(x))
end

################################################################################
#
#  IO
#
################################################################################


function show(io::IO, id::FunFldDiff)
  print(io, "(", id.f, ") d(", id.dx, ")")
end

################################################################################
#
#  Properties
#
################################################################################


function is_zero(df::FunFldDiff)
  return is_zero(df.f)
end

function function_field(df::FunFldDiff)
  return df.function_field
end

################################################################################
#
#  Arithmetic
#
################################################################################

function Base.:+(df::FunFldDiff, dg::FunFldDiff)
  f = df.f
  g = dg.f
  @assert parent(f) == parent(g)
  return FunFldDiff(f + g;dx = df.dx)
end

function Base.:-(df::FunFldDiff, dg::FunFldDiff)
  f = df.f
  g = dg.f
  @assert parent(f) == parent(g)
  return FunFldDiff(f - g;dx =  df.dx)
end

function Base.:-(df::FunFldDiff)
  return FunFldDiff(-df.f;dx =  df.dx)
end

function Base.:*(r::Generic.FunctionFieldElem, df::FunFldDiff)
  @assert parent(r) == parent(df.f)
  return FunFldDiff(r*df.f;dx = df.dx)
end

function Base.:*(r::GenOrdElem, df::FunFldDiff)
  F = function_field(df)
  return F(r) * df
end

function Base.:*(r::IntegerUnion, df::FunFldDiff)
  F = function_field(df)
  return F(r) * df
end

Base.:*(df::FunFldDiff, r::Generic.FunctionFieldElem) = r*df
Base.:*(df::FunFldDiff, r::GenOrdElem) = r*df
Base.:*(df::FunFldDiff, r::IntegerUnion) = r*df

@doc Markdown.doc"""
    //(df::FunFldDiff, dg::FunFldDiff) -> FunctionFieldElem
    
Return the function r such that r*df = dg.
"""
function Base.://(df::FunFldDiff, dg::FunFldDiff)
  return df.f//dg.f
end

function Base.://(df::FunFldDiff, r::Generic.FunctionFieldElem)
  @assert parent(r) == parent(df.f)
  return return FunFldDiff(df.f//r; dx = df.dx)
end

function Base.://(df::FunFldDiff, r::GenOrdElem)
  F = function_field(df)
  return df//F(r)
end

function Base.://(df::FunFldDiff, r::IntegerUnion)
  F = function_field(df)
  return df//(F(r))
end

################################################################################
#
#  Divisor
#
################################################################################

@doc Markdown.doc"""
    divisor(df::FunFldDiff) -> Divisor
    
Return the divisor corresponding to the differential form.
"""
function divisor(df::FunFldDiff)
  F = function_field(df)
  x = separating_element(F)
  return divisor(df.f)- 2*pole_divisor(F(x)) + different_divisor(F)
end

@doc Markdown.doc"""
    valuation(df::FunFldDiff, p::GenOrdIdl) -> Int
    
Return the valuation of the differential form at a prime.
"""
function valuation(df::FunFldDiff, p::GenOrdIdl)
  F = function_field(df)
  return valuation(divisor(df), p)
end

################################################################################
#
#  Basis of differentials
#
################################################################################


@doc Markdown.doc"""
    basis_of_differentials(F::FunctionField) -> Vector{FunFldDiff}
    
Return a basis of the first order differential forms of F.
"""
function basis_of_differentials(F::AbstractAlgebra.Generic.FunctionField)
  return map(t-> FunFldDiff(t), riemann_roch_space(canonical_divisor(F)))
end


