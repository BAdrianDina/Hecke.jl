export Amodule

add_assertion_scope(:ModLattice)

@attributes mutable struct ModAlgAss{S, T, U}
  base_ring::S
  dim::Int
  is_irreducible::Int # 0 not know
                     # 1 true
                     # 2 false
  is_abs_irreducible::Int
  degree_splitting_field::Int
                     # same as above
  algebra::U
  action_of_gens::Vector{T}
  action_of_gens_inverse::Vector{T}
  action_of_basis::Vector{T}
  isfree::Int
  free_rank::Int

  function ModAlgAss{T, U}(algebra::U; action_of_basis::Vector{T} = T[], action_of_gens::Vector{T} = T[]) where {T, U}
    S = typeof(base_ring(algebra))
    z = new{S, T, U}()
    z.isfree = 0
    z.free_rank = -1
    if length(action_of_basis) > 0
      z.action_of_basis = action_of_basis
      z.dim = nrows(action_of_basis[1])
    end
    if length(action_of_gens) > 0
      z.action_of_gens = action_of_gens
      if !isdefined(z.dim)
        z.dim = nrows(action_of_gens[1])
      end
    end
    z.algebra = algebra
    z.base_ring = base_ring(algebra)
    if z.dim == 1
      z.is_irreducible = 1
      z.is_abs_irreducible = 1
      z.degree_splitting_field = 1
    else
      z.is_irreducible = 0
      z.is_abs_irreducible = 0
      z.degree_splitting_field = 0
    end
    return z
  end

  function ModAlgAss{T}(;action_of_gens::Vector{T} = T[]) where {T}
    K = base_ring(action_of_gens[1])
    U = matrix_algebra_type(K)
    S = typeof(K)
    z = new{S, T, U}()
    z.action_of_gens = action_of_gens
    z.base_ring = base_ring(action_of_gens[1])
    z.dim = nrows(action_of_gens[1])
    z.isfree = 0
    z.free_rank = -1
    if z.dim == 1
      z.is_irreducible = 1
      z.is_abs_irreducible = 1
      z.degree_splitting_field = 1
    else
      z.is_irreducible = 0
      z.is_abs_irreducible = 0
      z.degree_splitting_field = 0
    end

    return z
  end
end

struct ModAlgAssElem{P, T}
  parent::P
  coordinates::Vector{T}
end

parent(x::ModAlgAssElem) = x.parent

function (V::ModAlgAss)(x::Vector)
  if parent(x[1]) === V.base_ring
    return ModAlgAssElem(V, x)
  else
    return ModAlgAssElem(V, convert(Vector{elem_type(V.base_ring)}, map(V.base_ring, x)))
  end
end

coordinates(x::ModAlgAssElem) = x.coordinates

function Base.:(+)(x::ModAlgAssElem, y::ModAlgAssElem)
  return parent(x)(coordinates(x) + coordinates(y))
end

function Base.:(*)(x::ModAlgAssElem, y::AbsAlgAssElem)
  @assert parent(y) === parent(x).algebra
  return parent(x)(coordinates(x) * action(parent(x), y))
end

function Base.:(*)(x::FieldElem, y::ModAlgAssElem)
  return parent(y)(x * coordinates(y))
end

function Base.:(==)(x::ModAlgAssElem{P, T}, y::ModAlgAssElem{P, T}) where {P, T}
  return parent(x) === parent(y) && coordinates(x) == coordinates(y)
end

function Base.show(io::IO, V::ModAlgAss)
  print(io, "Amodule over field of dimension ", V.dim)
  if has_algebra(V)
    print(io, " (with algebra defined))")
  end
end

################################################################################
#
#  Field access
#
################################################################################

function algebra(V::ModAlgAss)
  if !isdefined(V, :algebra)
    error("Algebra of module not defined")
  else
    return V.algebra
  end
end

@doc raw"""
    coefficient_ring(V::ModAlgAss) -> Field

Returns the coefficient ring of the module.
"""
coefficient_ring(V::ModAlgAss) = V.base_ring


function dim(V::ModAlgAss)
  return V.dim
end

@doc raw"""
    Amodule(A::AbsAlgAss, M::Vector{<:MatElem})

Given an algebra $A$ over a field $K$ and a list of $\dim(A)$ of square
matrices over $K$, construct the $A$-module with `basis(A)[i]` acting
via `M[i]` from the right.
"""
function Amodule(A::AbsAlgAss, M::Vector{<:MatElem})
  @assert length(M) == length(basis(A))
  return ModAlgAss{eltype(M), typeof(A)}(A, action_of_basis = M)
end

@doc raw"""
    Amodule(M::Vector{<:MatElem})

Given a list `M` of square matrices over a field $K$, construct the module
for the free algebra with the generators acting via `M[i]` from the right.

Note that the free algebra will not be constructed and the resulting
object has no associated algebra.
"""
function Amodule(M::Vector{<:MatElem})
  return ModAlgAss{eltype(M)}(action_of_gens = M)
end

################################################################################
#
#  Predicates
#
################################################################################

@doc raw"""
    has_algebra(V::ModAlgAss) -> Bool

Returns whether the module was defined explicitly using an algebra.
"""
has_algebra(V::ModAlgAss) = isdefined(V, :algebra)

@doc raw"""
    has_matrix_action(V::ModAlgAss) -> Bool

Returns whether the action on the module is given by matrices.
"""
function has_matrix_action(V::ModAlgAss{S, T, U}) where {S, T, U}
  if T <: MatElem
    return true
  else
    return false
  end
end

################################################################################
#
#  Action
#
################################################################################

function action_of_basis(V::ModAlgAss)
  if isdefined(V, :action_of_basis)
    return V.action_of_basis
  else
    throw(NotImplemented())
  end
end

function action_of_basis(V::ModAlgAss, i::Int)
  if isdefined(V, :action_of_basis)
    return V.action_of_basis[i]
  else
    throw(NotImplemented())
  end
end

function action_of_gens(V::ModAlgAss)
  return V.action_of_gens
end

function action_of_gens_inverse(V::ModAlgAss)
  if isdefined(V, :action_of_gens_inverse)
    return V.action_of_gens_inverse
  else
    V.action_of_gens_inverse = inv.(V.action_of_gens)
    return V.action_of_gens_inverse
  end
end

@doc raw"""
    action(V::ModAlgAss{_, MatElem, _}, x::AbsAlgAssElem)

Given a $A$-module $V$ for an algebra $A$ with action given by matrices, and an
element $x$ of $A$, returns the action of $x$.
"""
function action(V::ModAlgAss{<:Any, <: MatElem, <:Any}, x::AbsAlgAssElem)
  @req parent(x) == algebra(V) "Algebra of module must be parent of element"
  cx = coefficients(x)
  M = cx[1] * action_of_basis(V, 1)
  for i in 2:length(cx)
    N = cx[i] * action_of_basis(V, i)
    M = add!(M, M, N)
  end
  return M
end

function action_of_word(V::ModAlgAss{<: Any, <: MatElem}, w::Vector{Int})
  gens = action_of_gens(V)
  gens_inv = action_of_gens_inverse(V)
  v = V.action_of_gens[1]^0
  for k in w
    if k > 0
      v = v * gens[k]
    else
      v = v * gens_inv[-k]
    end
  end
  return v
end

@doc raw"""
    action(V::ModAlgAss) -> Vector

Given a module $V$, returns the action on $V$. If no algebra is defined,
these will be generators, otherwise these will be the action of `basis(A)`.
"""
function action(V::ModAlgAss)
  if !has_algebra(V)
    return V.action_of_gens
  else
    return action_of_basis(V)
  end
end

function action_of_order_basis(V::ModAlgAss{S, T, U}, O::AlgAssAbsOrd) where {S, T, U}
  s = get_attribute(V, :order_action)
  if s === nothing
    t = Dict{typeof(O), Vector{T}}()
    set_attribute!(V, :order_action => t)
  else
    t = s::Dict{typeof(O), Vector{T}}
    if haskey(t, O)
      return t[O]::Vector{T}
    end
  end
  z = T[action(V, elem_in_algebra(y)) for y in basis(O, copy = false)]
  t[O] = z
  return z
end

# Internal function to give the action in a consistent way
# If there is no algebra, just returns the action
# If there is an algebra, the minimal number of generators
# is returned.
function consistent_action(V::T, W::T) where {T <: ModAlgAss}
  if !has_algebra(V)
    @assert !has_algebra(W)
  else
    @assert has_algebra(W)
    @assert algebra(V) === algebra(W)
  end

  if !has_algebra(V)
    @assert length(V.action_of_gens) == length(W.action_of_gens)
    return (V.action_of_gens, W.action_of_gens)
  end

  if !isdefined(V, :action_of_gens) || !isdefined(W, :action_of_gens)
    return (V.action_of_basis, W.action_of_basis)
  else
    return (V.action_of_gens, W.action_of_gens)
  end
end

################################################################################
#
#  Irreducibility
#
################################################################################

# TODO: make this check absolute irreducibility before
function is_irreducible_known(M::ModAlgAss)
  return M.is_irreducible != 0
end

function is_irreducible(M::ModAlgAss)
  if M.is_irreducible != 0
    return M.is_irreducible == 1
  else
    if !(coefficient_ring(M) isa FinField)
      error("NotImplemented: Coefficient ring must be a finite field")
    end
    fl, N = meataxe(M)
    if fl
      M.is_irreducible = 1
    else
      M.is_irreducible = 2
    end
    return fl
  end
end

function is_absolutely_irreducible_known(V::ModAlgAss)
  return V.is_abs_irreducible != 0
end

function is_absolutely_irreducible(V::ModAlgAss)
  if V.is_abs_irreducible != 0
    return V.is_abs_irreducible == 1
  end
  throw(NotImplemented())
end

#function composition_factors(V::ModAlgAss{<:FinField})
#  act = V.action_of_gens
#
#  cf = stub_composition_factors(act)
#
#  return [Amodule(c) for c in cf]
#end

function basis_of_hom(V, W)
  x, y = consistent_action(V, W)
  return stub_basis_hom_space(x, y)
end

################################################################################
#
#  Function stubs, filled in by Oscar
#
################################################################################

stub_composition_factors(a) = error("Load Oscar (or GAP) and try again")

stub_basis_hom_space(a, b) = error("Load Oscar (or GAP) and try again")

################################################################################
#
#  Homomorphism spaces
#
################################################################################

function regular_module(A::AbsAlgAss)
  K = base_ring(A)
  n = dim(A)
  B = basis(A)
  action_of_basis = [representation_matrix(b, :right) for b in B]
  M = Amodule(A, action_of_basis)
  M.isfree = 1
  M.free_rank = 1
  return M
end

################################################################################
#
#  Galois module
#
################################################################################

# Type to represent a Q[Gal(K)]-linear map K -> V
mutable struct NfToModAlgAssMor{S, T, U} <: Map{AnticNumberField, ModAlgAss{S, T, U}, HeckeMap, NfToModAlgAssMor}
  K::AnticNumberField
  mG::GrpGenToNfMorSet{NfToNfMor, AnticNumberField}
  V::ModAlgAss{S, T, U}
  M::QQMatrix
  Minv::QQMatrix

  function NfToModAlgAssMor{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end
end

function show(io::IO, f::NfToModAlgAssMor)
  print(io, "Galois module map from\n")
  print(io, f.K)
  print(io, "\nto\n")
  print(io, f.V)
end

function (f::NfToModAlgAssMor)(O::Union{NfAbsOrd, NfAbsOrdIdl})
  V = codomain(f)
  B = basis(O)
  G = group(A)
  ZG = Order(A, collect(G))
  return ideal_from_lattice_gens(A, ZG, [f(elem_in_nf(b)) for b in B], :right)
end

automorphism_map(f::NfToModAlgAssMor) = f.mG

function galois_module(K::AnticNumberField, aut::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(aut)
  A = FlintQQ[G]
  return _galois_module(K, A, aut, normal_basis_generator = normal_basis_generator)
end

function _galois_module(K::AnticNumberField, A, aut::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(aut)
  alpha = normal_basis_generator

  basis_alpha = Vector{elem_type(K)}(undef, dim(A))
  for (i, g) in enumerate(G)
    f = aut(g)
    basis_alpha[A.group_to_base[g]] = f(alpha)
  end

  M = zero_matrix(base_field(K), degree(K), degree(K))
  for i = 1:degree(K)
    a = basis_alpha[i]
    for j = 1:degree(K)
      M[i, j] = coeff(a, j - 1)
    end
  end

  invM = inv(M)

  z = NfToModAlgAssMor{QQField, QQMatrix, typeof(A)}()
  V = regular_module(A)
  z.K = K
  z.mG = aut
  z.V = V
  z.M = M
  z.Minv = invM

  return V, z
end

domain(f::NfToModAlgAssMor) = f.K

codomain(f::NfToModAlgAssMor) = f.V

function image(f::NfToModAlgAssMor, x::nf_elem)
  K = domain(f)
  @assert parent(x) === K
  V = codomain(f)

  t = zero_matrix(base_field(K), 1, degree(K))
  for i = 1:degree(K)
    t[1, i] = coeff(x, i - 1)
  end
  y = t*f.Minv
  return V([ y[1, i] for i = 1:degree(K) ])
end

function preimage(f::NfToModAlgAssMor, x::ModAlgAssElem)
  K = domain(f)
  y = coordinates(x)*f.M
  return K(y)
end
