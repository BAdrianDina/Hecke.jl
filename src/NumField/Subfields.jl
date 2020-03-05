export fixed_field, subfields

# Compute basis for the subfield of K that is generated by the elements of as.
function _subfield_basis(K::S, as::Vector{T}) where {
    S <: Union{AnticNumberField, Hecke.NfRel},
    T <: Union{nf_elem, Hecke.NfRelElem}
   }
  if isempty(as)
    return [gen(K)]
  end

  # Notation: k base field, K the ambient field, F the field generated by as

  k = base_field(K)

  d = degree(K)
  Kvs = VectorSpace(k,d)
  # We transition the coefficients of a in reverse order, so that the
  # first vector in the row reduced echelon form yields the highest
  # degree among all elements of Fas.
  (Fvs,phivs) = sub(Kvs, [Kvs([coeff(a,n) for n in d-1:-1:0])
                          for a in as])
  dF = length(Fvs.gens) # dim(Fvs)
  bs = as
  while !isempty(bs)
    nbs = elem_type(K)[]
    for b in bs
      abs = [a*b for a in as]
      abvs,_ = sub(Kvs, [Kvs([coeff(ab,n) for n in d-1:-1:0])
                         for ab in abs])
      (Fvs,phivs) = sub(Kvs, typeof(Fvs)[Fvs, abvs])
      if dF != length(Fvs.gens) # dim(Fvs)
        dF = length(Fvs.gens) # dim(Fvs)
        append!(nbs, abs)
      end
    end
    bs = nbs
  end

  kx = parent(K.pol)
  return [let Kv = phivs(v)
            K(kx([Kv[n] for n in d:-1:1]))
          end
          for v in gens(Fvs)]
end

function _improve_subfield_basis(K, bas)
  # First compute the maximal order of <bas> by intersecting and saturating
  # Then B_Ok = N * B_LLL_OK
  # Then B' defined as lllN * B_LLL_OK will hopefully be small
  OK = maximal_order(K)
  OKbmatinv = basis_mat_inv(OK, copy = false)
  basinOK = bas * matrix(FlintQQ, OKbmatinv.num) * fmpq(1, OKbmatinv.den)
  deno = fmpz(1)
  for i in 1:nrows(basinOK)
    for j in 1:ncols(basinOK)
      deno = lcm(deno, denominator(basinOK[i, j]))
    end
  end
  S = saturate(matrix(FlintZZ, basinOK * deno))
  SS = S * basis_matrix(OK, copy = false)
  lllOK = lll(OK)
  N = (SS * basis_mat_inv(lllOK)).num
  lllN = lll(N)
  maybesmaller = lllN * basis_matrix(lllOK)
  return maybesmaller
end

function _improve_subfield_basis_no_lll(K, bas)
  OK = maximal_order(K)
  OKbmatinv = basis_mat_inv(OK, copy = false)
  basinOK = bas * matrix(FlintQQ, OKbmatinv.num) * fmpq(1, OKbmatinv.den)
  deno = fmpz(1)
  for i in 1:nrows(basinOK)
    for j in 1:ncols(basinOK)
      deno = lcm(deno, denominator(basinOK[i, j]))
    end
  end
  S = saturate(matrix(FlintZZ, basinOK * deno))
  SS = S * basis_matrix(OK, copy = false)
  return SS
end

# Compute a primitive element given a basis of a subfield
function _subfield_primitive_element_from_basis(K::S, as::Vector{T}) where {
    S <: Union{AnticNumberField, Hecke.NfRel},
    T <: Union{nf_elem, Hecke.NfRelElem}
   }
  if isempty(as)
    return gen(K)
  end

  d = length(as)

  # First check basis elements
  i = findfirst(a -> degree(minpoly(a)) == d, as)
  if i <= d
    return as[i]
  end

  k = base_field(K)

  # Notation: cs the coefficients in a linear combination of the as, ca the dot
  # product of these vectors.
  cs = fmpz[zero(ZZ) for n in 1:d]
  cs[1] = one(ZZ)
  while true
    ca = sum(c*a for (c,a) in zip(cs,as))
    if degree(minpoly(ca)) == d
      return ca
    end

    # increment the components of cs
    cs[1] += 1
    let i = 2
      while i <= d && cs[i-1] > cs[i]+1
        cs[i-1] = zero(ZZ)
        cs[i] += 1
        i += 1
      end
    end
  end
end

#As above, but for AnticNumberField type
#In this case, we can use block system to find if an element is primitive.
function _subfield_primitive_element_from_basis(K::AnticNumberField, as::Vector{nf_elem})
  if isempty(as)
    return gen(K)
  end

  dsubfield = length(as)

  # First check basis elements
  Zx = PolynomialRing(FlintZZ, "x", cached = false)[1]
  f = Zx(K.pol*denominator(K.pol))
  p, d = _find_prime(f)

  #First, we search for elements that are primitive using block systems
  F = FlintFiniteField(p, d, "w", cached = false)[1]
  Ft = PolynomialRing(F, "t", cached = false)[1]
  ap = zero(Ft)
  fit!(ap, degree(K)+1)
  rt = roots(f, F)
  indices = Int[]
  for i = 1:length(as)
    b = _block(as[i], rt, ap)
    if length(b) == dsubfield
      push!(indices, i)
    end
  end

  #Now, we select the one of smallest T2 norm
  if !isempty(indices)
    a = as[indices[1]]
    I = t2(a)
    for i = 2:length(indices)
      t2n = t2(as[indices[i]])
      if t2n < I
        a = as[indices[i]]
        I = t2n
      end
    end
    return a
  end

  k = base_field(K)
  # Notation: cs the coefficients in a linear combination of the as, ca the dot
  # product of these vectors.
  cs = fmpz[zero(ZZ) for n in 1:dsubfield]
  cs[1] = one(ZZ)
  k = 0
  local I
  found = false
  while true
    ca = sum(c*a for (c,a) in zip(cs,as))
    b = _block(ca, rt, ap)
    if length(b) == dsubfield
      t2n = t2(a)
      if found
        k += 1
        if t2n < I
          a = ca
        end
        if k == 5
          return a
        end
      else
        found = true
        I = t2n
      end
    end

    # increment the components of cs
    cs[1] += 1
    let i = 2
      while i <= dsubfield && cs[i-1] > cs[i]+1
        cs[i-1] = zero(ZZ)
        cs[i] += 1
        i += 1
      end
    end
  end
end

################################################################################
#
#  Subfield
#
################################################################################

@doc Markdown.doc"""
    subfield(L::NumField, elt::Vector{<: NumFieldelem};
                          isbasis::Bool = false) -> NumField, Map

The simple number field $k$ generated by the elements of `elt` over the base
field $K$ of $L$ together with the embedding $k \to L$.

If isbasis is true, it is assumed that `elt` holds a $K$-basis of $k$.
"""
function subfield(K::NumField, elt::Vector{<:NumFieldElem}; isbasis::Bool = false)
  if length(elt) == 1
    return _subfield_from_primitive_element(K, elt[1])
  end

  if isbasis
    s = _subfield_primitive_element_from_basis(K, elt)
  else
    bas = _subfield_basis(K, elt)
    s = _subfield_primitive_element_from_basis(K, bas)
  end

  return _subfield_from_primitive_element(K, s)
end

function _subfield_from_primitive_element(K, s)
  f = minpoly(s)
  L,_ = NumberField(f, cached = false)
  return L, hom(L, K, s)
end

################################################################################
#
#  Fixed field
#
################################################################################

@doc Markdown.doc"""
    fixed_field(K::SimpleNumField,
                sigma::Map;
                simplify::Bool = true) -> NumberField, NfToNfMor

Given a number field $K$ and an automorphisms $\sigma$ of $K$, this function
returns the fixed field of $\sigma$ as a pair $(L, i)$ consisting of a number
field $L$ and an embedding of $L$ into $K$.

By default, the function tries to find a small defining polynomial of $L$. This
can be disabled by setting `simplify = false`.
"""
function fixed_field(K::SimpleNumField, sigma::T; simplify::Bool = true) where {T <: Union{NfToNfMor, NfRelToNfRelMor}}
  return fixed_field(K, T[sigma], simplify = simplify)
end

@doc Markdown.doc"""
    fixed_field(K::SimpleNumField, A::Vector{NfToNfMor}) -> NumberField, NfToNfMor

Given a number field $K$ and a set $A$ of automorphisms of $K$, this function
returns the fixed field of $A$ as a pair $(L, i)$ consisting of a number field
$L$ and an embedding of $L$ into $K$.

By default, the function tries to find a small defining polynomial of $L$. This
can be disabled by setting `simplify = false`.
"""
function fixed_field(K::SimpleNumField, A::Vector{T}; simplify::Bool = true) where {T <: Union{NfToNfMor, NfRelToNfRelMor}}
  autos = A

  # Everything is fixed by nothing :)
  if length(autos) == 0
    return K, id_hom(K)
  end

  F = base_field(K)
  a = gen(K)
  n = degree(K)
  ar_mat = Vector{dense_matrix_type(elem_type(F))}()
  v = Vector{elem_type(K)}(undef, n)
  for i in 1:length(autos)
    domain(autos[i]) !== codomain(autos[i]) && throw(error("Maps must be automorphisms"))
    domain(autos[i]) !== K && throw(error("Maps must be automorphisms of K"))
    o = one(K)
    # Compute the image of the basis 1,a,...,a^(n - 1) under autos[i] and write
    # the coordinates in a matrix. This is the matrix of autos[i] with respect
    # to 1,a,...a^(n - 1).
    as = autos[i](a)
    if a == as
      continue
    end
    v[1] = o
    for j in 2:n
      o = o * as
      v[j] = o
    end

    if isabsolute(K)
      bm = basis_matrix(v, FakeFmpqMat)
      # We have to be a bit careful (clever) since in the absolute case the
      # basis matrix is a FakeFmpqMat

      m = matrix(FlintQQ, bm.num)
      for j in 1:n
        m[j, j] = m[j, j] - bm.den # This is autos[i] - identity
      end
    else
      bm = basis_matrix(v)
      # In the generic case just subtract the identity
      m = bm - identity_matrix(F, degree(K))
    end

    push!(ar_mat, m)
  end

  if length(ar_mat) == 0
    return K, id_hom(K)
  else
    bigmatrix = hcat(ar_mat)
    k, Ker = kernel(bigmatrix, side = :left)
    bas = Vector{elem_type(K)}(undef, k)
    if isabsolute(K)
      # Try to find a small basis for absolute simple number fields
      if simplify
        KasFMat = _improve_subfield_basis(K, Ker)
        for i in 1:k
          bas[i] = elem_from_mat_row(K, KasFMat.num, i, KasFMat.den)
        end
      else
        #KasFMat = _improve_subfield_basis_no_lll(K, Ker)
        KasFMat = FakeFmpqMat(Ker)
        Ksat = saturate(KasFMat.num)
        Ksat = lll(Ksat)
        onee = one(fmpz)
        for i in 1:k
          #bas[i] = elem_from_mat_row(K, KasFMat.num, i, KasFMat.den)
          bas[i] = elem_from_mat_row(K, Ksat, i, onee)
        end
      end
    else
      for i in 1:k
        bas[i] = elem_from_mat_row(K, Ker, i)
      end
    end

    return subfield(K, bas, isbasis = true)
  end
end


