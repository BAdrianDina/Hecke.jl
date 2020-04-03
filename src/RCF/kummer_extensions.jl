abstract type AbelianExt end

mutable struct KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Vector{FacElem{nf_elem, AnticNumberField}}

  AutG::GrpAbFinGen
  frob_cache::Dict{NfOrdIdl, GrpAbFinGenElem}
  frob_gens::Tuple{Vector{NfOrdIdl}, Vector{GrpAbFinGenElem}}
  gen_mod_nth_power::Vector{FacElem{nf_elem, AnticNumberField}}
  eval_mod_nth::Vector{nf_elem}
  
  function KummerExt()
    return new()
  end
end

function Base.show(io::IO, K::KummerExt)
  if isdefined(K.AutG, :snf)
    print(io, "KummerExt with structure $(K.AutG.snf)")
  else
    print(io, "KummerExt with structure $([K.AutG.rels[i, i] for i=1:ngens(K.AutG)])")
  end
end

@doc Markdown.doc"""
    kummer_extension(n::Int, gens::Vector{FacElem{nf_elem, AnticNumberField}}) -> KummerExt
Creates the Kummer extension of exponent $n$ generated by the elements in 'gens'.
"""
function kummer_extension(n::Int, gen::Vector{FacElem{nf_elem, AnticNumberField}})
  K = KummerExt()
  k = base_ring(gen[1])
  zeta, o = torsion_units_gen_order(k)
  @assert o % n == 0
  K.zeta = zeta^div(o, n)
  K.n = n
  K.gen = gen
  K.AutG = GrpAbFinGen(fmpz[n for i=gen])
  K.frob_cache = Dict{NfOrdIdl, GrpAbFinGenElem}()
  return K
end

function kummer_extension(exps::Array{Int, 1}, gens::Vector{FacElem{nf_elem, AnticNumberField}})
  K = KummerExt()
  k = base_ring(gens[1])
  zeta, o = torsion_units_gen_order(k)
  n = lcm(exps)
  @assert o % n == 0

  K.zeta = zeta^div(o, n)
  K.n = n
  K.gen = gens
  K.AutG = abelian_group(exps)
  K.frob_cache = Dict{NfOrdIdl, GrpAbFinGenElem}()
  return K
end

function kummer_extension(n::Int, gen::Array{nf_elem, 1})
  g = FacElem{nf_elem, AnticNumberField}[FacElem(x) for x in gen]
  return kummer_extension(n, g)
end

###############################################################################
#
#  Base Field
#
###############################################################################

function base_field(K::KummerExt)
  return base_ring(K.gen[1])
end

###############################################################################
#
#  Exponent of a Kummer extension
#
###############################################################################

function exponent(K::KummerExt)
  return Int(exponent(K.AutG))
end

###############################################################################
#
#  Degree
#
###############################################################################

function degree(K::KummerExt)
  return Int(order(K.AutG))
end

###############################################################################
#
#  IsCyclic
#
###############################################################################

function iscyclic(K::KummerExt)
  return isone(length(K.gen)) || iscyclic(K.AutG)
end

###############################################################################
#
#  From Kummer Extension to Number Field
#
###############################################################################

function number_field(K::KummerExt)
  k = base_field(K)
  kt = PolynomialRing(k, "t", cached = false)[1]
  pols = Array{elem_type(kt), 1}(undef, length(K.gen))
  for i = 1:length(pols)
    p = Vector{nf_elem}(undef, Int(order(K.AutG[i]))+1)
    p[1] = -evaluate(K.gen[i])
    for i = 2:Int(order(K.AutG[i]))
      p[i] = zero(k)
    end 
    p[end] = one(k)
    pols[i] = kt(p)
  end
  return number_field(pols, check = false, cached = false)
end

###############################################################################
#
#  Computation of Frobenius automorphisms
#
###############################################################################


# the Frobenius at p in K:
#K is an extension of k, p a prime in k,
#returns a vector in (Z/nZ)^r representing the Frob
@doc Markdown.doc"""
    canonical_frobenius(p::NfOrdIdl, K::KummerExt) -> GrpAbFinGenElem
Computes the element of the automorphism group of $K$ corresponding to the
Frobenius automorphism induced by the prime ideal $p$ of the base field of $K$.
It fails if the prime is a index divisor or if p divides the given generators
of $K$
"""
function canonical_frobenius(p::NfOrdIdl, K::KummerExt)
  @assert norm(p) % K.n == 1
  if haskey(K.frob_cache, p)
    return K.frob_cache[p]
  end
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end
  if !fits(Int, minimum(p, copy = false))
    return canonical_frobenius_fmpz(p, K)
  end

  if degree(p) != 1
    F, mF = ResidueFieldSmall(Zk, p)
    mF1 = NfToFqNmodMor_easy(mF, number_field(Zk))
    aut = _compute_frob(K, mF1, p)
  else
    F2, mF2 = ResidueFieldSmallDegree1(Zk, p)
    mF3 = NfToGFMor_easy(mF2, number_field(Zk))
    aut = _compute_frob(K, mF3, p)
  end
  z = K.AutG(aut)
  K.frob_cache[p] = z
  return z
end

function _compute_frob(K, mF, p)
  z_p = image(mF, K.zeta)^(K.n-1)
 
  # K = k(sqrt[n_i](gen[i]) for i=1:length(gen)), an automorphism will be
  # K[i] -> zeta^divexact(n, n_i) * ? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  aut = Array{fmpz, 1}(undef, length(K.gen))
  for j = 1:length(K.gen)
    ord_genj = Int(order(K.AutG[j]))
    ex = div(norm(p)-1, ord_genj)
    if isdefined(K, :gen_mod_nth_power)
      mu = image(mF, K.gen_mod_nth_power[j])^ex
    else
      mu = image(mF, K.gen[j], K.n)^ex  # can throw bad prime!
    end
    i = 0
    z_pj = z_p^divexact(K.n, ord_genj)
    while !isone(mu)
      i += 1
      @assert i <= K.n
      mu = mul!(mu, mu, z_pj)
    end
    aut[j] = fmpz(i)
  end
  return aut
end

function canonical_frobenius_fmpz(p::NfOrdIdl, K::KummerExt)
  @assert norm(p) % K.n == 1
  if haskey(K.frob_cache, p)
    return K.frob_cache[p]
  end
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end


  F, mF = ResidueField(Zk, p)
  #_mF = extend_easy(mF, number_field(Zk))
  mF1 = NfToFqMor_easy(mF, number_field(Zk))
  z_p = image(mF1, K.zeta)^(K.n-1)

  # K = k(sqrt[n_i](gen[i]) for i=1:length(gen)), an automorphism will be
  # K[i] -> zeta^divexact(n, n_i) * ? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  aut = Array{fmpz, 1}(undef, length(K.gen))
  for j = 1:length(K.gen)
    ord_genj = Int(order(K.AutG[j]))
    ex = div(norm(p)-1, ord_genj)
    if isdefined(K, :gen_mod_nth_power)
      mu = image(mF1, K.gen_mod_nth_power[j])^ex
    else
      mu = image(mF1, K.gen[j], K.n)^ex  # can throw bad prime!
    end
    i = 0
    z_pj = z_p^divexact(K.n, ord_genj)
    while !isone(mu)
      i += 1
      @assert i <= K.n
      mul!(mu, mu, z_pj)
    end
    aut[j] = fmpz(i)
  end
  z = K.AutG(aut)
  K.frob_cache[p] = z
  return z
end

#In this function, we are computing the image of $sqrt[n](g) under the Frobenius automorphism of p
function canonical_frobenius(p::NfOrdIdl, K::KummerExt, g::FacElem{nf_elem})
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    throw(BadPrime(p))
  end

  if !fits(Int, minimum(p, copy = false))
    error("Oops")
  end
  
  @assert norm(p) % K.n == 1
  ex = div(norm(p)-1, K.n)
  
  #K = sqrt[n](gen), an automorphism will be
  # K[i] -> zeta^? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p
  
  if degree(p) != 1
    F, mF = ResidueFieldSmall(Zk, p)
    mF1 = extend_easy(mF, nf(Zk))
    z_p = inv(mF1(K.zeta))
    mu = image(mF1, g, K.n)^ex  # can throw bad prime!
    i = 0
    while true
      if isone(mu)
        break
      end
      i += 1
      @assert i <= K.n
      mu = mul!(mu, mu, z_p)
    end
    return i
  else
    F2, mF2 = ResidueFieldSmallDegree1(Zk, p)
    mF3 = extend_easy(mF2, nf(Zk))
    z_p1 = inv(mF3(K.zeta))
    mu1 = image(mF3, g, K.n)^ex  # can throw bad prime!
    i = 0
    while true
      if isone(mu1)
        break
      end
      i += 1
      @assert i <= K.n
      mu1 = mul!(mu1, mu1, z_p1)
    end
    return i
  end
end

################################################################################
#
#  IsSubfield
#
################################################################################

@doc Markdown.doc"""
    issubfield(K::KummerExt, L::KummerExt) -> Bool, Vector{Tuple{nf_elem, Vector{Int}}}
Given two kummer extensions of a base field $k$, returns true and and the data 
to define an injection from K to L if K is a subfield of L. Otherwise
the function returns false and a some meaningless data.
"""
function issubfield(K::KummerExt, L::KummerExt)
  @assert base_field(K) == base_field(L)  
  @assert divisible(exponent(L), exponent(K))
  #First, find prime number that might be ramified.
  norms = Vector{fmpz}(undef, length(K.gen)+length(L.gen)+1)
  for i = 1:length(K.gen)
    norms[i] = numerator(norm(K.gen[i]))
  end
  for i = 1:length(L.gen)
    norms[i+length(K.gen)] = numerator(norm(L.gen[i]))
  end
  norms[end] = fmpz(exponent(L))
  norms = coprime_base(norms)
  coprime_to = lcm(norms)
  res = Vector{Tuple{FacElem{nf_elem, AnticNumberField}, Vector{Int}}}(undef, length(K.gen))
  lP = find_gens(L, Vector{FacElem{nf_elem, AnticNumberField}}[K.gen], coprime_to)
  for i = 1:length(K.gen)
    fl, coord, rt = _find_embedding(L, K.gen[i], Int(order(K.AutG[i])), lP)
    if !fl
      return fl, res
    end
    res[i] = (rt, Int[Int(coord[j]) for j = 1:length(L.gen)])
  end
  return true, res
end


################################################################################
#
#  Kummer failure
#
################################################################################

@doc Markdown.doc"""
    kummer_failure(x::nf_elem, M::Int, N::Int) -> Int
Computes the the quotient of N and $[K(\zeta_M, \sqrt[N](x))\colon K(\zeta_M)]$, 
where $K$ is the field containing $x$ and $N$ divides $M$.  
"""
function kummer_failure(x::nf_elem, M::Int, N::Int)
  @assert divisible(M, N)
  K = parent(x)
  CE = cyclotomic_extension(K, M)
  el = CE.mp[2](x)
  lp = factor(N)
  deg = 1
  for (p, v) in lp
    e = 1
    y = x
    for i = v:-1:1
      fl, y = ispower(y, Int(p), with_roots_unity = true)
      if !fl
        e = v
        break
      end
    end
    deg *= Int(p)^e
  end
  @assert divisible(N, deg)
  return divexact(N, deg)
end
