################################################################################
#
#          EllCrv/Finite.jl : Elliptic curves over finite fields
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# (C) 2016 Tommy Hofmann
# (C) 2016 Robin Ammon
# (C) 2016 Sofia Brenner
# (C) 2022 Jeroen Hanselman
#
################################################################################

export hasse_interval, order, order_via_exhaustive_search, order_via_bsgs, order_via_legendre,
       order_via_schoof, trace_of_frobenius, rand, elem_order_bsgs, is_supersingular,
       is_ordinary, is_probable_supersingular, supersingular_polynomial

################################################################################
#
#  Random point
#
################################################################################

Random.gentype(::Type{EllCrv{T}}) where {T} = EllCrvPt{T}

@doc raw"""
    rand(E::EllCrv) -> EllCrvPt

Return a random point on the elliptic curve $E$ defined over a finite field.
"""
function rand(rng::AbstractRNG, Esp::Random.SamplerTrivial{<:EllCrv})
  # Algorithm 6 of Miller, "The Weil Pairing, and Its Efficient Calculation"
  E = Esp[]
  R = base_field(E)

  if E.short == false
    while true
      return_infinity = rand(rng, 0:order(R))
      if return_infinity == 1
        return infinity(E)
      end
      # choose random x-coordinate and check if there exists a corresponding y-coordinate
      x = rand(rng, R)
      a1, a2, a3, a4, a6 = a_invars(E)
      Ry, y = polynomial_ring(R,"y")
      f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
      ys = roots(f)
      if length(ys) != 0
        t = rand(rng, ys)
        P = E([x,t])
        return P
      end
    end
  end

  while true
  # choose random x-coordinate and check if it is a square in F_q
  # if not, choose new x-coordinate
    return_infinity = rand(rng, 0:order(R))
    if return_infinity == 1
      return infinity(E)
    end

    x = rand(rng, R)
    _,_,_, a4, a6 = a_invars(E)
    Ry, y = polynomial_ring(R,"y")
    f = y^2 - x^3 - a4*x - a6
    ys = roots(f)
      if length(ys)!=0
        t = rand(rng, ys)
        P = E([x,t])
        return P
      end
  end
end

################################################################################
#
# Order via exhaustive search
#
################################################################################

@doc raw"""
    order_via_exhaustive_search(E::EllCrv{FinFieldElem) -> ZZRingElem

Calculate the number of points on an elliptic curve $E$ over a finite field
$\mathbf Z/p\mathbf Z$ using exhaustive search.
"""
function order_via_exhaustive_search(E::EllCrv{T}) where T<:FinFieldElem
  R = base_field(E)
  order = FlintZZ(1)
  a1, a2, a3, a4, a6 = a_invars(E)
  Ry, y = polynomial_ring(R,"y")
  for x = R
    f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
    ys = roots(f)
    order += length(ys)
  end

  return order
end

################################################################################
#
# Order via Legendre symbol
#
################################################################################

# Th. 4.14
@doc raw"""
    order_via_legendre(E::EllCrv{Generic.ResidueRingElem{ZZRingElem}) -> ZZRingElem

Calculate the number of points on an elliptic curve $E$ over a finite field
$\mathbf Z/p\mathbf Z$ using the Legendre symbol. It is assumed that $p$ is
prime.
"""
function order_via_legendre(E::EllCrv{T}) where T<:FinFieldElem


  R = base_field(E)
  p = characteristic(R)
  q = order(R)
  grouporder = FlintZZ(0)
  p == 0 && error("Base field must be finite")

  if p != q
    error("Finite field must have degree 1")
  end

  if E.short == false
    E = short_weierstrass_model(E)[1]
  end
  _, _, _, a4, a6 = a_invars(E)
  x = FlintZZ(0)

  while x < p
    C = x^3 + a4*x + a6
    Cnew = lift(ZZ, C) # convert to ZZRingElem
    a = jacobi_symbol(Cnew, p) # can be used to compute (C/F_p) since p prime
    grouporder = grouporder + a
    x = x + 1
  end

  grouporder = grouporder + p + 1

#  return grouporder
end

################################################################################
#
#  Hasse interval
#
################################################################################

@doc raw"""
    hasse_interval(E::EllCrv) -> (ZZRingElem, ZZRingElem)

Given an elliptic curve $E$ over a finite field $\mathbf F$, return an array
`[l, b]` of integers, such that $l \leq \#E(\mathbf F) \leq b$ using
Hasse's theorem.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(3), [1, 2]);

julia> hasse_interval(E)
(0, 8)
```
"""
function hasse_interval(E::EllCrv{<: FinFieldElem})
  R = base_field(E)
  characteristic(R) == 0 && error("Base field must be finite")
  q = order(R)
  s = isqrtrem(q)[1] # sqrt(q) rounded down

  l = q + 1 - 2*(s + 1)
  b = q + 1 + 2*(s + 1)

  return l, b
end

# section 4.3.4
@doc raw"""
    elem_order_bsgs(P::EllCrvPt) -> ZZRingElem

Calculate the order of a point $P$ on an elliptic curve given over a finite
field using BSGS.
"""
function elem_order_bsgs(P::EllCrvPt{T}) where T<:FinFieldElem
  R = base_field(P.parent)
  p = characteristic(R)
  p == 0 && error("Base field must be finite")
  q = order(R) # R = F_q

  # step 1
  Q = Int(q + 1) * P

  # step 2
  m = Int(ceil(Int(q)^(1//4)))

  list_points = []
  for j = 0:m
    S = j*P
    push!(list_points, S)
  end

  # step 3
  k = -m
  H = (2*m)*P
  M = FlintZZ(0) # initialize M, so that it is known after the while loop

  while k < m + 1
    Snew = Q + (k*H)

    i = 1
    while i < m + 2 # is there a match?
      if Snew == list_points[i]
        M = q + 1 + (2*m*k) - (i-1)

        if M != 0
          i = m + 2 # leave both while loops
          k = m + 1
        else
          i = i + 1 # search on if M == 0
        end

      elseif Snew == -(list_points[i])
        M = q + 1 + (2*m*k) + (i-1) # step 4

        if M != 0
          i = m + 2 # leave both while loops
          k = m + 1
        else
          i = i + 1 # search on if M == 0
        end
      else
        i = i + 1
      end
    end

    k = k + 1
  end

  # step 5
  gotostep5 = true
  while gotostep5
    fac = factor(M)
    primefactors = []
    for i in fac
      push!(primefactors, i[1])
    end
    r = length(primefactors)

    # step 6
    i = 1
    while i < (r + 1)
      U = Int(divexact(M, primefactors[i]))*P
      if U.is_infinite == true
        M = divexact(M, primefactors[i])
        i = r + 2  # leave while-loop
      else
        i = i + 1
      end
    end

    if i == r + 1  # then (M/p_i)P != oo for all i
      gotostep5 = false
    end
  end

  return abs(ZZ(M))
end

@doc raw"""
    order(P::EllCrvPt, [fac::Fac{ZZRingElem}]) -> ZZRingElem

Given a point $P$ on an elliptic curve $E$ over a finite field, return the order
of this point.

Optionally, one can supply the factorization of a multiple of the point order,
for example the order of $E$.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> P = E([17, 65]);

julia> order(P)
100

julia> fac = factor(order(E))
1 * 5^2 * 2^2

julia> order(P, fac)
100
```
"""
function order(P::EllCrvPt{T}) where T<:FinFieldElem
  return elem_order_bsgs(P)
end

function order(P::EllCrvPt{T}, fac::Fac{ZZRingElem}) where T<:FinFieldElem
  return _order_elem_via_fac(P, fac)
end

function _order_elem_via_fac(P::EllCrvPt{<:FinFieldElem}, fn = _order_factored(parent(P)))
  E = parent(P)
  n = order(E)
  o = one(ZZ)
  for (p, e) in fn
    q = p^e
    m = divexact(n, q)
    Q = m*P # order dividing q = p^e
    for i in 0:e
      if is_infinite(Q)
        break
      else
        o = o * p
        Q = p * Q
      end
    end
  end
  return o
end

################################################################################
#
#  Order via BSGS
#
################################################################################

@doc raw"""
    order_via_bsgs(E::EllCrv) -> Vector{ZZRingElem}

Calculate candidates for the number of points on an elliptic curve $E$ given
over a finite field $\mathbf F_q$, using the baby step giant step method. If
$q$ prime, $q > 229$, then the order is determined uniquely by this algorithm.
It is assumed that the characteristic is not 2.
"""
function order_via_bsgs(E::EllCrv{T}) where T<:FinFieldElem
  R = base_field(E)
  p = characteristic(R)
  p == 0 && error("Base field must be finite")

  q = order(R)

  if (p == 2)
    error("Characteristic must not be 2")
  end
  #char also not 3 right?
  if E.short == false
    E = short_weierstrass_model(E)[1]
  end

  Nposs = FlintZZ(1)
  h = hasse_interval(E)
  l = h[1]
  b = h[2]

  counter = 0
  runwhile = true

  # if Nposs is greater than interval length, there is only one multiple of
  # Nposs in the interval, so stop
  # Also, if lcm does not change in 10(?) consecutive loops, leave while loop
  while (Nposs <= (b-l)) && (runwhile == true)

    P = rand(E)
    ord = elem_order_bsgs(P)

    if lcm(ord, Nposs) == Nposs
      counter = counter + 1
    else
      Nposs = lcm(ord, Nposs)
      counter = 0
    end

    if counter > 10 # maybe take another criterion
      runwhile = false
    end

  end

  if runwhile == false # could not determine group order uniquely
    candidates = ZZRingElem[]
    Ncand = divrem(l, Nposs)[1]*Nposs
    if Ncand != 0
      push!(candidates, Ncand)
    end

    Ncand = Ncand + Nposs

    while Ncand < b # compute all possible group orders using Hasse's theorem
      push!(candidates, Ncand)
      Ncand = Ncand + Nposs
    end

    output = candidates

  else # group order is determined
    N = (divrem(l, Nposs)[1] + 1) * Nposs
    output = [N]
  end

  if (p == q) && (p > 229) && (length(output) != 1)
  # group order is uniquely determined, but by quadratic twist

    d = R(0)
    boolie = true
    while boolie # get a quadratic non-residue mod p
      d = rand(R)
      if is_square(d)[1] == false
        boolie = false
      end
    end
    _, _, _, a4, a6 = a_invars(E)
    Eprime = elliptic_curve([a4*d^2, a6*d^3]) # quadratic twist
    bb = order_via_bsgs(Eprime)[1]
    output = [2*p + 2 - bb]
  end

  return output
end


################################################################################
#	Point counting via Shoof-Elkies-Atkin's algorithm; this implementation is 
#	based on Chapter VII in Elliptic Curves in Cryptography (ECC) by 
#	Blake-Seroussi-Smart.
#   
################################################################################

################################################################################
#	Exammple:
#   F = GF(131)
#	E = EllipticCurve(F, [1,23])
#  	phi_l = classical_modular_polynomial(5)	
#	evaluete_classical_modular_polynomial_at_j_invariant(phi_l, j_invariant(E))
################################################################################
@doc raw"""
	modular_polynomial_at_j_invariant(phi_l::Poly) -> Poly

This algorithm is computing the value of the classical modular polynomial at the 
point P = (x, j), where j is the j-invariant of an elliptic curve defined over Fq. 
Function returns a polynomial in Fq[x]. 
"""
function modular_polynomial_at_j_invariant(phil, j)
	#where T<: Integer
	# TODO: I am not sure yet, it PolyElem is the correct data type; this needs to be checked! And to check which data type is phil.
	# how do I define j to be of type field element?
	# this function should be only for internal usage.
	
	R = parent(j)
	RR, (x, y) = polynomial_ring( R, ["x","y"] )
	philFq = change_base_ring( RR, phil )
	
	# evaluate phi_lFq on x and on the j-invariant of E. 
	philFqj = philFq(x, j)
	
	# in order to change phi_lFqj to a polynomial in Fq[x], we
	# need to do a hack because I do not know yet a better solution. 
	# we need to change it later to something more smart; 
	Rx, x = polynomial_ring(R, "x")
	coeffs = collect(coefficients(philFqj))
	expons = collect(exponent_vectors(philFqj))
	expons = [ t[1] for t in expons ]
	philFqj = sum( [ coeffs[i]*x^(expons[i]) for i in length(coeffs):-1:1 ] )
	
return philFq, philFqj	
end

@doc raw"""
	partial_derivatives_classical_modular_polynomial(phi_l::Poly) -> Poly, Poly

This algorithm is computing the partial derivatives of the classical modular 
polynomial. 
"""
function partial_derivative_classical_modular_polynomial(phil) 
	#where T<: Integer
	# TODO: I am not sure yet, it PolyElem is the correct data type; this needs to be checked! 
	
	# TODO: We need some general checks before beginning:
	
	
	################################################################################
	#	Exammple:
	#   @time phil = classical_modular_polynomial(5)
	#	@time Hecke.partial_derivative_classical_modular_polynomial(phil)
	############################################################################
	
	R = parent(phil)
	x = R[1]
	y = R[2]
	
	coeffs = collect(coefficients(phil))
	expons = collect(exponent_vectors(phil))
	expons_x = [ tup[1] for tup in expons ]
	expons_y = [ tup[2] for tup in expons ]
	
	#compute partial derivatives;
	expons_xx = map(x -> x > 0 ? x - 1 : x, expons_x)
	expons_yy = map(y -> y > 0 ? y - 1 : y, expons_y)
	
	
	# check if the computation is correct; 
	if length(expons_x) != length(expons_xx)
		error("exponent array of fx anf (fx)' need to have the same length")
	end
	
	if length(expons_y) != length(expons_yy)
		error("exponent array of fy anf (fy)' need to have the same length")
	end
	
	for i in 1:length(expons_x)
		t = expons_x[i]
		tx = expons_xx[i]
		tup = tuple(t, tx)
		
		# correct are (t, tx) = (0, 0), (t, tx) = (1, 0), which  
		# is a special case of (t, tx) = (x^r, r*x^{r-1}).
		if !( ( tup == (0, 0) ) | ( tup == (1, 0) ) | ( tup == (t, t - 1) ) )
			error("wrong partial derivative computation")
		end 		
	end
	
	expons_xx_y = [ [ expons_xx[i], expons_y[i] ] for i in 1:length(expons) ]
	expons_x_yy = [ [ expons_x[i], expons_yy[i] ] for i in 1:length(expons) ]
	
	# construct partial derivatives;
	philx = sum( [ coeffs[i]*expons_x[i]*x^(expons_xx_y[i][1])*y^(expons_xx_y[i][2]) for i in 1:length(coeffs) ] )
	phily = sum( [ coeffs[i]*expons_y[i]*x^(expons_x_yy[i][1])*y^(expons_x_yy[i][2]) for i in 1:length(coeffs) ] )
	
	# TODO: we need here some checks that we do not return the 0-function;
	
	return philx, phily 	
end

@doc raw""" 
TODO: write documentation
"""
function compute_cks_coeffs(d, cks)

	if length(cks) >= d
		return cks
	end
	
	if length(cks) < 1
		error("#cks == 0")
	end
	
	k = length(cks) + 1
	R = parent(cks[1])
	
	return compute_cks_coeffs(d, append!(cks, [ R( R(3) * R( ( (k - R(2)) * (R(2)*k + R(3)) )^(-1) )  * R( sum(cks[j]*cks[k-1-j] for j in 1:k-2 ) ) ) ]))
end


@doc raw""" 
TODO: write documentation
"""
function Cw(d, x, cks)
	
	if length(cks) < d
		error("#cks < l. ")
	end
	
	R = parent(cks[1])
	f = sum( cks[k] * x^k for k in 1:d )
	
	# in order to construct the exp. function exp(f);
	# TODO: clarify if we expand f till degree(f).
	#RL, x = laurent_series_ring(R, degree(f)+1, "x")
	RL, x = laurent_series_ring(R, degree(f)^2, "x")
	
	coeffs = collect(coefficients(f))
	f_ = sum( coeffs[i+1] * x^(i) for i in 0:degree(f) )	
	
	return f_
end 

@doc raw""" 
Returns the i-th. coefficient of f(x).
"""
# not in use at the moment; instead we use 
# the function exp_Aw_i2. 
function exp_Aw_i(Aw_d, i)
	
	# constant coefficient corresp. to entry 1 in coeffs.
	coeffs = collect(coefficients(Aw_d))
	
	if length(coeffs) <= 1
		return coeffs[1]
	end
	
	return coeffs[i+1]
end

function exp_Aw_i2(Aw_d, i)
	return coeff(Aw_d, i)
end

# not in use at the moment; instead we use 
# the function Cw_j2.
@doc raw""" 
Returns the i-th. coefficient of f(x).
"""
function Cw_j(Cw_d, j)
	# constant coefficient corresp. to entry 1 in coeffs.
	coeffs = collect(coefficients(Cw_d))
		
	if (j+1) > length(Cw_d)
		return 0
	end
	
	return coeffs[j+1]
end

function Cw_j2(Cw_d, j)
	return coeff(Cw_d, j)
end









@doc raw""" 
TODO: write description
"""
function compute_Fli(d, Flds, Aw_d, Cw_d)
	
	if length(Flds) > d 
		return Flds
	end
	
	if ( length(Aw_d) <= 0 ) || ( length(Cw_d) <= 0 ) 
		error("#Aw_d <= 0, and(or) #Cw_d <= 0. ")
	end
	
	R = parent(Flds[1])
	i = length(Flds) 
	
	Fli_d_i = Aw_i(Aw_d, i) - sum( Flds[i] * sum( binomial(d-i+k, k-j) * Cw_j(Cw_d^(k-j), j) for j in 0:k ) for k in 1:i ) 
	
	return compute_Fli(d, append!(Flds, [Fli_d_i]), Aw_d, Cw_d)
end


@doc raw""" 
	exp_Aw(d, x, p1, l, cks, cks_t)

Input: positive integer d, variable x, finite field elements p1, l, and arrays cks, cks_t corresponding
to coefficients ck, ck_tilde from formulae (VII.22) in ECC.
Output: the right hand-side of formulae (VII.23) in ECC.  
"""
function exp_Aw(d, x, p1, l, cks, cks_t)
	
	"TODO: I need tom check if I indeed need to constuct these complicated Laurent-series, or
	if I can solve my problem of constructing exp(f) in a much easier way!
	"
	
	if (length(cks) < d) || (length(cks_t) < d) || (length(cks) != length(cks_t))
		error("error in #cks, and/or #cks_t. ")
	end
	
	R = parent(cks[1]) 
	
	f =  (- R( p1 * R(2)^(-1)) * x) - sum( R((2*i + 1) * (2*i + 2))^(-1) * R(cks_t[i] - l*cks[i]) * x^(i + 1) for i in 1:d )	
	
	# in order to construct the function exp(f);
	# TODO: clarify if we expand f till degree(f).
	#RL, x = laurent_series_ring(R, degree(f)+1, "x")
	RL, x = laurent_series_ring(R, degree(f)^2, "x")
	
	coeffs = collect(coefficients(f))
	f_lr = sum( coeffs[i+1] * x^(i) for i in 0:degree(f) )
	f_lr_exp = exp(f_lr)
	
	return f_lr_exp, f_lr 
end

@doc raw""" 
TODO: write documentation
"""
function compute_Fl(E, d, l, p1, cks, cks_t)
	# test example
	# F = GF(131)
	# E = EllipticCurve(F, [1,23])
	# l = 5
	# test example
		
	# (1) Einen Algorithmus schreiben um gegeben eine ganze Zahl d = N alle c_k für k höchstens N zu bestimmen; verwende dazu (VII.22); dies soll über allgemeinen Körper funktioniert, damit du formelle Ausdrücke bestimmen kannst. --> done.
	
	# Hast du (1), so kannst du die Potenzreihe zwischen den Exp-Klammern in (VII.23) bis Präzision N bestimmen. Wir brauchen dann einen zweiten Teil:
	# (2) Einen Algorithmus, um eine Potenzreihe effektiv exponentieren zu können, und einen, um zwei dieser Reihen effektiv zu multiplizieren. 
	# An diesem Punkt kennst du die Koeffizienten von A (w) durch Exponentiation, und die von C (w)^{k - j} auch. Dann brauchst du nur noch

	# (3) Eine Weise, um die Rekursion (VII.24) zu berechnen. Aber die Formel hast du ja, also das geht.

	
	if (length(cks) < d) || (length(cks_t) < d) || (length(cks) != length(cks_t))
		error("error in #cks, and/or #cks_t. ")
	end
	
	R = parent(cks[1])
	RR, x = polynomial_ring(R, "x")
	
	Cw_d = Cw(d, x, cks)
	exp_Aw_d, Aw_d = exp_Aw(d, x, p1, l, cks, cks_t)
	
	# I am working hwere at the moment ############
	# there is an error inside!!!
	# I need a function who is converting Laurent Series to 
	# polynomials over Fp.
	Fl_dis = compute_Fli(d, [R(1)], Aw_d, Cw_d)
	# I am working here at the moment ############
	
	
	
	maxFl = length(Fl_dis) - 1
	Fl_monomials = [ x^t for t in maxFl:-1:0 ]
	F_l = sum( Fl_dis[i] * Fl_monomials[i] for i in 1:maxFl+1 )
	
	# for test reasons compute division polkynomial f_l(x)
	# and check if F_l(x) | f_l(x)
	f_ls = division_polynomial_univariate(E, l)
	f_l = f_ls[1]
	
	if gcd(F_l, f_l) == 1
		return false
	end
		
	return true, Fl
end

@doc raw"""
	isElkiesPrime(l::Integers) -> Integers

Given an integer l, this function checks if l is an Elkies prime; this test
is based on the splitting type of the modular polynomial phi_l(x, j(E)) in ZZ[x, y],
respectively in Fq[x].
This algorithm is based on [Proposition 7.2, Elliptic Curves in Cryptography, Blake-Seroussi-Smart]. 
"""
function isElkiesPrime(l::Int, E::EllCrv{T}) where T<:FinFieldElem
	
    R = base_field(E)
    q = order(R)
    p = characteristic(R)
	j = j_invariant(E)
	
	# some test
	if is_prime(l) == false
		error("integer l must be prime")
	end 
	
	if l > 59
		error("Database only contains classical modular polynomials up to level 59")
	end 
	
	######################
	# the Atkin modular polynomial has smaller coefficients as the classical modular polynomial. Can we use it???
	# fMA = atkin_modular_polynomial(l)
	######################
	
	# the classical l.th modular polynomial:
	phi_l = classical_modular_polynomial(l)	
	phi_lFq, phi_lFqj = modular_polynomial_at_j_invariant(phi_l, j)
	
	# decompose the modular polynomial;	
	prod_irred_fac = collect( factor( phi_lFqj ))
	irred_facts = []
	for tup in prod_irred_fac
		irred_fac = tup[1]
		append!(irred_facts, [irred_fac] )
		
		exp = tup[2]
		if exp > 1
			append!(irred_facts, [irred_fac for k in 1:(exp - 1) ] )
		end
	end
	
	# some further test on irreducibility;
	if sum([ true & is_irreducible(f) for f in irred_facts ]) != length(irred_facts)
		error("not all factors of the l-th. mod. polynomial are irreducible")
	end
	
	
	# TODO: Maybe we can get the degree immediately from the variable prod_irred_fac above; the degree of the polynomial is deg_f = length(collect(coeffs(f))) - 1 for f in prod_irred_fac;
	deg_irred_facts = [ degree(f) for f in irred_facts ]
	
	
	# check [Proposition VII.2, Elliptic Curves in Cryptography, Blake-Seroussi-Smart]
	# l is an Elkies prime iff; 
	# I.1 deg_irred_facts = [1, l], up to permutation, or 
	# I.2 deg_irred_facts = [1, 1, ..., 1], or 
	# II. deg_irred_facts = [1, 1, r, ..., r] and r|l-1.
	# III. if deg_irred_facts = [r, r, ..., r], with r > 1, then l is an Atkin prime.
	
	if ( length(deg_irred_facts) == 2 ) & ( sum(deg_irred_facts) == l+1 ) # case I.1;
		return true, irred_facts
	elseif sum(deg_irred_facts) == length(deg_irred_facts) # case I.2;	
		return true, irred_facts
	elseif 	( count(g -> g == 1, deg_irred_facts) == 2 ) & 
			( count(g -> g > 1, deg_irred_facts) == (length(deg_irred_facts) - 2 )) # case II;
		return true, irred_facts  
	end

	# case III
	# the second return value corresponds to the value r for the Atkin procedure
	r = deg_irred_facts[1]
	
	return false, r
end

@doc raw"""
	ElkiesProcedure(l::Int, E::EllCrv{T}, irred_facts_of_phil::Vector{Any}) where T<:FinFieldElem
This algorithm is [Algorithm 7.3, Elliptic Curves in Cryptography, Blake-Seroussi-Smart]. 
"""

#function ElkiesProcedure(l::Int, E::EllCrv{T}, irred_facts_of_phil::Vector{Any}) where T<:FinFieldElem
function ElkiesProcedure(l::Int, E::EllCrv{T}) where T<:FinFieldElem
	
    R = base_field(E)
    q = order(R)
    p = characteristic(R)
	j = j_invariant(E)
	
	# some test before; E needs to be defined over Fp.
	if order(R) != p 
		error("Base field in this procedure has to be Fp")
	end
	
	# the classical l.th modular polynomial:
	phi_l = classical_modular_polynomial(l)	
	
	# compute derivatives with results as polynomials in ZZ[x, y]; 
	# later, we will convert these polynomials to Fp[x, y]. 
	phi_lx, phi_ly = partial_derivative_classical_modular_polynomial(phi_l)
	phi_lxx, phi_lxy = partial_derivative_classical_modular_polynomial(phi_lx)
	phi_lyx, phi_lyy = partial_derivative_classical_modular_polynomial(phi_ly)
	
	# some tests;
	if phi_lxy != phi_lyx 
		error("erroneous computation; phi_lxy ≠ phi_lyx")
	end
	
	# TODOD: Remove afterwards;
	# from now on all computations are in Fp, see [Chapter VII.4, ECC];
	# to determine the factor Fl(x), of degree d := (l-1)/2, we proceed as follows:
	# 1. given E over Fp, j = j(E), determine a j-invariant j_tilde of an isogenous curve, by determining a root of the modular polynomial   phil(x, j), in other words phil(j_tilde, j) = 0.
	# 2. given j_tilde, determine coefficients a_tilde, b_tilde in Fp of an isogenous curve E_tilde: Y^2 = x^3 + a_tilde*X + b_tilde,          j_tilde = j(E_tilde).
	# 3. knowing the isogenous curve E_tilde, and the kernel of the isogeny phi: E --> E_tilde, compute the sum of the x-coord. of the points in ker(phi). From (E, E_tilde) and the sum of the x-coord. of the points in ker(phi), determine Fl(x):
	# our implementation is Algorithm VII.3 in ECC, and by defining steps, we always mean the steps in this algorithm.
	
	
 	# phi_lFq in Fp[x, y], phi_lFqj in Fp[x];
	phi_lFq, phi_lFqj = modular_polynomial_at_j_invariant(phi_l, j)
	

	RR, x = polynomial_ring(R, "x")
	Frobf = x^p - x
	
	# some test
	if parent(Frobf) != parent(phi_lFqj)
		error("not same universe for polynomials Frobf and phi_lFqj")
	end
	
	# the first approach uses classical modular polynomials, see chapter 
	# VII.4.1 in ECC;
	f_gcd = gcd(Frobf, phi_lFqj)
	
	# some tests related to the degree of f_gcd;
	if degree(f_gcd) > 2
		error("degree of gcd(x^p - x, phi_lj) is greater then 2")
	end
	
	facts = collect(factor(f_gcd))
	facts = [ tup[1] for tup in facts ]
	root_facts = [ roots(f) for f in facts ]
	root_facts = [ tup[1] for tup in root_facts ]
	
	
	# step 4;
	# for any of the two roots in root_facts, we compute 
	# Equation VII.17 on page 126 in ECC, over Fp; 
	_, _, _, a_4, a_6 = a_invars(E)
	
	
	# d = (l-1)/2; it corresponds to the degree of the  
	# division polynomial factor Fl(x).
	d = Int((l-1)//2)
	
	for j_tilde in root_facts
		
		# we construct two to E isogenies curves;
		E4q_modp = R( - 48 * a_4 )
		E6q_modp = R( 864 * a_6 )
		j_prime = R( - E6q_modp * j * E4q_modp^(-1) )
	
	
		# step 5; 
		nom = R(j_prime * phi_lx(j, j_tilde))
		denom = R(l * phi_ly(j, j_tilde))
		if denom == R(0)
			continue
		end
		j_t_p = - nom * denom^(-1)
	
		# step 6;
		a_tilde = R(- j_t_p^2 * (48 * j_tilde * (j_tilde - 1728))^(-1))
		b_tilde = R(- j_t_p^3 * (864 * j_tilde^2 * (j_tilde - 1728))^(-1))	
	
		# step 7; 
		E4ql_modp = R(- 48 * a_tilde)
		E6ql_modp = R(864 * b_tilde)
	
		# step 8;
		nom = R( j_prime^2 * phi_lxx(j, j_tilde) 
			 + 2*l*j_prime*j_t_p*phi_lxy(j, j_tilde) 
			 + l^2*j_t_p^2*phi_lyy(j, j_tilde) )
		denom = R( j_prime * phi_lx(j, j_tilde) ) 
	
		if denom == R(0)
			#error("denominator is zero")
			continue
		end
		rat_rep = R( - nom * denom^(-1) )
	
		# step 9: 
		A = R(l*R(2)^(-1)*rat_rep)
		B = R(l*R(4)^(-1)*(E4q_modp^2 * E6q_modp^(-1) - l*E4ql_modp^2 * E6ql_modp^(-1)))
		C = R(l*R(3)^(-1)*(E6q_modp * E4q_modp^(-1) - l*E6ql_modp * E4ql_modp^(-1)))
		p1 = R( A + B + C )
	 
		cks = compute_cks_coeffs( d, [ R( - a_4 * R(5)^(-1) ), R( - a_6 * R(7)^(-1) ) ] )
		cks_t = compute_cks_coeffs(d, [R( - a_tilde * l^4 * R(5)^(-1) ), R( - b_tilde * l^6 * R(7)^(-1) )] )
		
		######### I am working hwere at the moment ############################.
		# TODO: I am here in the code, 25.11.23
		test, Fl = compute_Fl(E, d, l, p1, cks, cks_t)
		######### I am working hwere at the moment ############################.
		
		
	
		
		
		#TODO: There is an error inside; it happens for l = 2.
		if gcd(F_l, f_l) != 1
			# we need only one factor of f_l(x), namely one F_l(x)
			if degree(F_l) == floor(Int, ((l-1)//2))
				return F_l
			else
				error("error: degree(F_l) = ", degree(F_l), " and not ", floor(Int, (l-1)/2))
			end
		else
			error("error: gcd(F_l, f_l) = ", gcd(F_l, f_l))
		end
	end	
end

@doc raw"""
	AtkinProcedure(l::Int, E::EllCrv{T}) where T<:FinFieldElem
	
This algorithm is [Algorithm VII.4, Elliptic Curves in Cryptography, Blake-Seroussi-Smart]. 
"""
function AtkinProcedure(l::Int, r::Int, E::EllCrv{T}) where T<:FinFieldElem
	###################################################################
	#	Exammple:
	#   F = GF(131)
	#	E = EllipticCurve(F, [1,23])
	#   l = 17
	#   test, r = Hecke.isElkiesPrime(l, E)
	# 	Tl = Hecke.AtkinProcedure(l, r, E)
	###################################################################
	
    R = base_field(E)
    q = order(R)
    p = characteristic(R)
	
	Fl = GF(l)
	Flsq, g = FiniteField(l, 2, "g")
	S = [ g^(Int(i*(l^2-1)/r)) for i in 1:r-1 if gcd(i,r) == 1 ]
	
	if length(S) == 0
		error("#S = 0")
	end
	
	S_decomp = []
	for x in S
		append!(S_decomp, [[i, j] for i in 0:order(Fl) for j in 0:order(Fl) if i*g + j == x ])
	end
	
	if length(S_decomp) == 0
		error("#S_decomp = 0")
	end
	
	println("l = ", l)
	# compute the inverse of 2 mod l:
	# I guess there is a better solution in Julia
	# which I still didn't find yet.
	inv_2 = [ i for i in 1:l if (i*2%l) == 1][1]
	println("2^-1 = ", inv_2)
	
	Tl = []
	for tup in S_decomp
		g1 = tup[2]
		z = q*(g1+1)
		z *= inv_2
		z %= l
		
		try
			x = sqrtmod(ZZ(z), ZZ(l))
			append!(Tl, [[2*x, -2*x]])
		catch
			continue
		end
	end
	
	Tl = Set(Tl)
	return Tl
end







# TODO: implement without quotient ring
@doc raw"""
	FindEigenvalueModl(Flx, E) -> Integers
This algorithm is based on [Proposition 7.2, Elliptic Curves in Cryptography, Blake-Seroussi-Smart]. 
"""
function FindEigenvalueModl(Flx, E)
	R = base_field(E)
	Rxy, (x, y) = polynomial_ring(R, ["x", "y"]) 
	
    #Lx, X = polynomial_ring(L, "X")
    #Lxy, Y = polynomial_ring(Lx, "Y")
	
	return 1
end

################################################################################
#
#  SEA algorithm; notes by Bogdan Adrian Dina based on the book 
#  Elliptic Curves in Cryptography (ECC) by Blake-Seroussi-Smart
#  
################################################################################
@doc raw"""
    order_via_SEA(E::EllCrv) -> ZZRingElem

Given an elliptic curve $E$ over a finite field $\mathbf F$,
this function computes the order of $E(\mathbf F)$ using Schoof's-Elkies's-Atkin's  
algorithm. (The characteristic must not be $2$ or $3$.)
"""
function order_via_SEA(E::EllCrv{T}) where T<:FinFieldElem
    R = base_field(E)
    q = order(R)
    p = characteristic(R)

	# some test:
	if (p == 0)
		error("Characteristic must not be 0")
	end
    if (p == 2) || (p == 3) 
	  error("Characteristic 2,3 not implemented yet")
    end
	
	
	# TODO: we will imoplement a version for the case where char(R) = 2;
	# see VII.5 for a detailed discussion and algorithm.
	
	# TODO: determining the trace modulo a prime power;
	# see VII.6 for a detailed discussion and algorithm.
	
	
    if E.short == false
      E = short_weierstrass_model(E)[1]
    end
	
	
	# main procedure:
	A = Set()
	E_ = Set()
	
	M = 1 
	M_max = 4*isqrt(q)
	l = 2
	
	while M < M_max
		
		println("l = ", l)
		
		if l == p
			continue
		end
		
		test, irred_facts_of_phil = isElkiesPrime(l, E)
		
		if test == true
			Flx = ElkiesProcedure(l, E)	
			
			# TODO: continue here with another approcah instead of defining a 
			# quotient ring RR = Fq[x, y]/(E, Flx):
			# this is the bottleneck of the computation.
			
			#lambda = FindEigenvalueModl(Flx, E)
			lambda = 1
			
			# compute the inverse of lambda mod l:
			# I guess there is a better solution in Julia
			# which I still didn't find yet.
			inv_lambda = [ i for i in 1:l if ((i*lambda)%l) == 1][1]
			
			t = (lambda + (q * inv_lambda)) % l
			
			append!(E_, [t, l])
		else
			r = irred_facts_of_phil
			println("r = ", r)
			Tl = AtkinProcedure(l, r, E)
			push!(A, [Tl, l])
		end
		
		M *= l
		l = next_prime(l)
		println("\n")
	end 
	
	# recover t 
	return q + 1 - t	
end 


################################################################################
#
#  Schoof's algorithm
#  Notes by Bogdan Adrian Dina; these notes are based on the books Elliptic and 
#  Hyperelliptic Curve Cryptography by H. Cohen and G. Frey and The Arithmetic
#  of Elliptic Curves by J.H. Silverman
#  Recall that |E(Fp)| = p + 1 − t with t the trace of the  Frobenius endomorphism phi_p and by Hasse’s Theorem, we have |t| \leq 2*p^(1/2). 
#  The main idea of Schoof’s algorithm is: 
#  1. compute t modulo small primes ell_1,..., ell_r s.t. prod_{i = 1}^r ell_i \leq 4*p^(1/2).
#  2. The trace t can be determined using the Chinese remainder theorem. 
#
################################################################################

@doc raw"""
    order_via_schoof(E::EllCrv) -> ZZRingElem

Given an elliptic curve $E$ over a finite field $\mathbf F$,
this function computes the order of $E(\mathbf F)$ using Schoof's algorithm
The characteristic must not be $2$ or $3$.
"""
function order_via_schoof(E::EllCrv{T}) where T<:FinFieldElem
  R = base_field(E)
  q = order(R)
  p = characteristic(R)

  if (p == 2) || (p == 3) || (p == 0)
    error("Characteristic must not be 2 or 3 or 0")
  end

  if E.short == false
    E = short_weierstrass_model(E)[1]
  end

  # step 1: get suitable set S of prime numbers
  sqrt_q = isqrtrem(q)[1]
  S = prime_set(4*(sqrt_q + 1), p)

  L = length(S)
  product = 1

  # step 2: compute t (mod l) for every l in S
  t_mod_l = []
  for i = 1:L
    a = S[i]
    push!(t_mod_l, t_mod_prime(S[i], E))
    product = product * S[i]
  end

  # step 3: use chinese remainder theorem to get value of t
  t = 0
  for i = 1:L
    n_i = div(product, S[i])
    B = residue_ring(FlintZZ, S[i], cached = false)
    M_i = inv(B(n_i))
    M_i = M_i.data
    t = t + (M_i * n_i * t_mod_l[i])
  end

  t = mod(t, product)
  if t > product//2
    t = t - product
  end

  return (q + 1 - t)::ZZRingElem
end


function fn_from_schoof(E::EllCrv, n::Int, x)

  poly = division_polynomial_univariate(E, n, x)[2]
    if iseven(n)
      poly = 2*poly
    end

  return(poly)

end


function fn_from_schoof2(E::EllCrv, n::Int, x)

  R = base_field(E)
  S, y = polynomial_ring(parent(x),"y")

  f = psi_poly_field(E, n, x, y)

 # println("f: $f, $(degree(f))")
    A = E.a_invars[4]
    B = E.a_invars[5]

  g = x^3 + A*x + B

  if isodd(n)
    return replace_all_squares(f, g)
  else
    return replace_all_squares(divexact(f, y), g)
  end


end

#prime_set(M::Nemo.ZZRingElem, char::Nemo.ZZRingElem) -> Array{Nemo.ZZRingElem}
#  returns a set S of primes with:
# 1) char not contained in S
# 2) product of elements in S is greater than M
function prime_set(M, char)
  S = Nemo.ZZRingElem[]

  p = 1
  product = 1

  while product < M
    p = next_prime(p)

    if p != char
      push!(S,p)
      product = product * p
    end
  end

  return S
end

# t_mod_prime(l::Nemo.ZZRingElem, E::EllCrv) -> Nemo.ZZRingElem
# determines the value of t modulo some prime l (used in Schoof's algorithm)
function t_mod_prime(l, E)
  R = base_field(E)
  q = order(R)
  q_int = Int(q)
  l = Int(l)

  S, x = polynomial_ring(R, "x")
  T, y = polynomial_ring(S, "y")
  Z = Native.GF(l, cached = false)

  _, _, _, a4, a6 = a_invars(E)
  f = x^3 + a4*x + a6
  fl = division_polynomial_univariate(E, l, x)[2]
  if iseven(l)
    fl = 2*fl
  end
  U = residue_ring(S, fl)

  PsiPoly = [] # list of psi-polynomials
  for i = -1:(l + 1)
    push!(PsiPoly, psi_poly_field(E, i, x, y)) # Psi[n] is now found in PsiPoly[n+2]
  end

  #Fnschoof = [] # list of the fn- functions # Psi[n] is now found in PsiPoly[n+2]
  #for i = -1:(l + 1)
  #  push!(Fnschoof, fn_from_schoof(E,i,x))
  #end

  #push!(PsiPoly, -one(T))
  #push!(PsiPoly, zero(T))
  #for i = 1:(l + 1)
  #  push!(PsiPoly, division_polynomial(E, i, x, y)) # Psi[n] is now found in PsiPoly[n+2]
  #end


  Fnschoof = [] # list of the fn- functions # Psi[n] is now found in PsiPoly[n+2]
  push!(Fnschoof, -one(S))
  push!(Fnschoof, zero(S))
  for i = 1:(l + 1)
    poly = division_polynomial_univariate(E, i, x)[2]
    if iseven(i)
      poly = 2*poly
    end
    push!(Fnschoof,poly)
  end

  # case where l == 2. value of t mod l determined by some gcd, see p. 124
  if l == 2
    x_q = powermod(x, q_int, f)
    ggt = gcd(f, x_q - x)
    if ggt == 1
      t = FlintZZ(1)
    else
      t = FlintZZ(0)
    end

    return t
  end

  # case where l != 2
  k = Int(mod(q, l)) # reduce q mod l
  k_mod = Z(k)

  fk = Fnschoof[k+2]
  fkme = Fnschoof[k+1]
  fkpe = Fnschoof[k+3]
  fkpz = Fnschoof[k+4]

  # is there a nonzero P = (x,y) in E[l] with phi^2(P) == +-kP ?
  if mod(k,2) == 0
    g = U( (powermod(x, q_int^2, fl) - x) * fk^2 * f + fkme * fkpe).data
    ggT = gcd(g, fl)
  else
    g = U( (powermod(x, q_int^2, fl) - x) * fk^2 + fkme * fkpe * f).data
    ggT = gcd(g, fl)
  end

  if ggT != 1 # case 1
    if jacobi_symbol(FlintZZ(k), FlintZZ(l)) == -1
      return FlintZZ(0)
    else
      # need square root of q (mod l)
      w = is_square_with_sqrt(k_mod)[2]
      if w.data < 0
        w = w + l
      end
      w_int = Int(w.data)

      fw = Fnschoof[w_int+2]
      fwme = Fnschoof[w_int+1]
      fwpe = Fnschoof[w_int+3]

      if mod(w_int, 2) == 0
        g = U((powermod(x,q_int,fl) - x) * fw^2*f + fwme*fwpe).data # reduce mod fl
        ggT = gcd(g, fl)
      else
        g = U((powermod(x,q_int,fl) - x) * fw^2 + fwme*fwpe*f).data
        ggT = gcd(g, fl)
      end

      if ggT == 1
        return FlintZZ(0)
      else
        fwmz = Fnschoof[w_int]
        fwpz = Fnschoof[w_int+4]

        if mod(w_int, 2) == 0
          g = U(4 * powermod(f,div(q_int + 3, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
          ggT2 = gcd(g, fl)
        else
          g = U(4 * powermod(f,div(q_int - 1, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
          ggT2 = gcd(g, fl)
        end

        if ggT2 == 1
          return -2*ZZRingElem(w.data)
        else
          return 2*ZZRingElem(w.data)
        end
      end
    end
  else # case 2
    Fkmz = PsiPoly[k]
    Fkme = PsiPoly[k+1]
    Fk = PsiPoly[k+2]
    Fkpe = PsiPoly[k+3]
    Fkpz = PsiPoly[k+4]

    alpha = Fkpz*psi_power_mod_poly(k-1, E, x, y, 2, fl) - Fkmz*psi_power_mod_poly(k+1, E, x, y, 2, fl) - 4*powermod(f, div(q_int^2+1, 2), fl)*psi_power_mod_poly(k, E, x, y, 3, fl)
    beta = ((x - powermod(x, (q_int^2), fl))*psi_power_mod_poly(k, E, x, y, 2, fl)- Fkme*Fkpe)*4*y*Fk

    tau = 1
    while tau < l

      ftaumz = PsiPoly[tau]
      ftaume = PsiPoly[tau+1]
      ftau = PsiPoly[tau+2]
      ftaupe = PsiPoly[tau+3]
      ftaupz = PsiPoly[tau+4]

      fntaumz = Fnschoof[tau]
      fntaume = Fnschoof[tau+1]
      fntaupe = Fnschoof[tau+3]
      fntaupz = Fnschoof[tau+4]

      gammahelp = powermod(fntaupz*fntaume^2- fntaumz * fntaupe^2,q_int,fl)

      if mod(tau, 2) == 0
        gamma = y * powermod(f,div(q_int-1,2),fl) * gammahelp
      else
        gamma = powermod(f,q_int,fl) * gammahelp
      end

      monster1 = ((Fkme*Fkpe - psi_power_mod_poly(k, E, x, y, 2, fl)*(powermod(x, q_int^2, fl) + powermod(x, q_int, fl) + x)) * beta^2 + psi_power_mod_poly(k, E, x, y, 2, fl)*alpha^2) * psi_power_mod_poly(tau, E, x, y, 2*q_int, fl) + psi_power_mod_poly(tau-1, E, x,y,q_int,fl)*psi_power_mod_poly(tau+1, E, x,y,q_int, fl)*beta^2*psi_power_mod_poly(k, E, x, y, 2, fl)

      if divrem(degree(monster1), 2)[2] == 1
        monster1 = divexact(monster1, y)
      end

      monster1_1 = replace_all_squares_modulo(monster1, f, fl)
      monster1_2 = U(monster1_1).data # monster1_1 reduced

      if monster1_2 != 0
        tau = tau + 1
      else
        monster2 = 4*y*powermod(f,div(q_int-1,2),fl)*psi_power_mod_poly(tau,E,x,y,3*q_int,fl) * (alpha * (((2*powermod(x, q_int^2, fl) + x) * psi_power_mod_poly(k,E,x,y,2,fl) - Fkme*Fkpe )*beta^2 - alpha^2*psi_power_mod_poly(k,E,x,y,2,fl)) - y*powermod(f,div(q_int^2-1,2),fl)*beta^3 * Fk^2) - beta^3*psi_power_mod_poly(k,E,x,y,2,fl)*gamma

        if divrem(degree(monster2), 2)[2] == 1
          monster2 = divexact(monster2, y)
        end

        monster2_1 = replace_all_squares_modulo(monster2, f,fl)
        monster2_2 = U(monster2_1).data # monster2_1 mod fl

        if monster2_2 != 0
          tau = tau + 1
        else
          return tau
        end
      end
    end
  end
end


# Division polynomials in general for an elliptic curve over an arbitrary field

# standard division polynomial Psi (as needed in Schoof's algorithm)
function psi_poly_field(E::EllCrv, n::Int, x, y)

    R = base_field(E)
    A = E.a_invars[4]
    B = E.a_invars[5]

    if n == -1
        return -y^0
    elseif n == 0
        return zero(parent(y))
    elseif n == 1
        return y^0
    elseif n == 2
        return 2*y
    elseif n == 3
        return (3*x^4 + 6*(A)*x^2 + 12*(B)*x - (A)^2)*y^0
    elseif n == 4
        return 4*y*(x^6 + 5*(A)*x^4 + 20*(B)*x^3 - 5*(A)^2*x^2 - 4*(A)*(B)*x - 8*(B)^2 - (A)^3)
    elseif mod(n,2) == 0
        m = div(n,2)
        return divexact( (psi_poly_field(E,m,x,y))*(psi_poly_field(E,m+2,x,y)*psi_poly_field(E,m-1,x,y)^2 - psi_poly_field(E,m-2,x,y)*psi_poly_field(E,m+1,x,y)^2), 2*y)
    else m = div(n-1,2)
        return psi_poly_field(E,m+2,x,y)*psi_poly_field(E,m,x,y)^3 - psi_poly_field(E,m-1,x,y)*psi_poly_field(E,m+1,x,y)^3
    end
end

# computes psi_n^power mod g
function psi_power_mod_poly(n, E, x, y, power, g)

    A = E.a_invars[4]
    B = E.a_invars[5]

    fn = fn_from_schoof2(E, n, x)
    f = x^3 + A*x + B
    p = powermod(fn,power,g)

    if mod(n, 2) == 0
        if mod(power, 2) == 0
            p1 = powermod(f, div(power, 2), g)
        else
            p1 = powermod(f, div(power - 1, 2), g) * y
        end
    else p1 = 1
    end

    return p * p1
end


function replace_all_squares(f, g)
    # assumes that f is in Z[x,y^2] and g in Z[x]. Replaces y^2 with g.
    # the result will be in Z[x]
    z = zero(parent(g)) # this is the zero in Z[x]
    d = div(degree(f), 2) # degree of f in y^2 should be even
    for i in 0:d
        z = z + coeff(f, 2*i)*g^i
    end
    return z
end

################################################################################
#
#  Point counting
#
################################################################################

@doc raw"""
    order(E::EllCrv{<: FinFieldElem}) -> ZZRingElem

Given an elliptic curve $E$ over a finite field $\mathbf F$, compute
$\#E(\mathbf F)$.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> order(E)
100
```
"""
@attr fmpz function order(E::EllCrv{T}) where T<:FinFieldElem
  R = base_field(E)
  p = characteristic(R)
  q = order(R)

  p == 0 && error("Characteristic must be nonzero")

  # char 2 or 3
  if p == 2 || p == 3
    return ZZ(order_via_exhaustive_search(E))
  end

  A = order_via_bsgs(E)
  if length(A) == 1
    return ZZ(A[1])
  end
  return ZZ(order_via_schoof(E)) # bsgs may only return candidate list
end

# don't use @attr, because I need that the attribute has this
# name
function _order_factored(E::EllCrv{<:FinFieldElem})
  return get_attribute!(E, :order_factored) do
    return factor(order(E))
  end::Fac{fmpz}
end

@doc raw"""
    trace_of_frobenius(E::EllCrv{FinFieldElem}) -> Int

Return the trace of the Frobenius endomorphism on the elliptic curve $E$
over $\mathbf{F}_q$. This is equal to $q + 1 - n$ where n is the
number of points on $E$ over $\mathbf{F}_q$.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> trace_of_frobenius(E) == 101 + 1 - order(E)
true
```
"""
function trace_of_frobenius(E::EllCrv{T}) where T<:FinFieldElem
  return order(base_field(E))+1 - order(E)
end

@doc raw"""
    trace_of_frobenius(E::EllCrv{<: FinFieldElem}, r::Int) -> ZZRingElem

Return the trace of the $r$-th power of the Frobenius endomorphism on
the elliptic curve $E$.

```jldoctest
julia> E = elliptic_curve(GF(101, 2), [1, 2]);

julia> trace_of_frobenius(E, 2)
18802
```
"""
function trace_of_frobenius(E::EllCrv{T}, n::Int) where T<:FinFieldElem
  K = base_field(E)
  q = order(K)
  a = q +1 - order(E)
  R, x = polynomial_ring(QQ)
  f = x^2 - a*x + q
  if is_irreducible(f)
    L, alpha = number_field(f)
    return ZZ(trace(alpha^n))
  else
    _alpha = roots(f)[1]
    return 2 * ZZ(_alpha^n)
  end
end

################################################################################
#
#  Supersingular Elliptic Curves
#
################################################################################


#Following Identifying supersingular elliptic curves - Andrew V. Sutherland
@doc raw"""
    is_supersingular(E::EllCrv{T}) where T <: FinFieldElem
Return true when the elliptic curve is supersingular. The result is proven to be correct.
"""
function is_supersingular(E::EllCrv{T}) where T <: FinFieldElem
  K = base_field(E)

  p = characteristic(K)
  j = j_invariant(E)

  if j^(p^2) != j
    return false
  end

  if p<= 3
    return j == 0
  end

  L = Native.GF(p, 2)
  Lx, X = polynomial_ring(L, "X")
  Lxy, Y = polynomial_ring(Lx, "Y")
  Phi2 = X^3 + Y^3 - X^2*Y^2 + 1488*(X^2*Y + Y^2*X) - 162000*(X^2 + Y^2) + 40773375*X*Y + 8748000000*(X + Y) - 157464000000000

  jL = _embed_into_p2(j, L)

  js = roots(Phi2(jL))

  if length(js) < 3
    return false
  end

  newjs = [jL, jL, jL]
  f = elem_type(Lx)[zero(Lx), zero(Lx), zero(Lx)]

  m = nbits(p) - 1
  for k in (1 : m)
    for i in (1 : 3)
      f[i] = divexact(Phi2(js[i]), X - newjs[i])
      newjs[i] = js[i]
      froots = roots(f[i])
      if isempty(froots)
        return false
      end
      js[i] = froots[1]
    end
  end
  return true
end

function _to_z(a::Union{fpFieldElem, FpFieldElem})
  return lift(a)
end

function _to_z(a::Union{fqPolyRepFieldElem, FqPolyRepFieldElem})
  return coeff(a, 0)
end

function _to_z(a::FqFieldElem)
  return lift(ZZ, a)
end

function _embed_into_p2(j, L)
  K = parent(j)
  # The easy case
  if degree(K) == 1
    return L(_to_z(j))
  else
    p = minpoly(j)
    # Easy case
    if degree(p) <= 1
      return L(_to_z(j))
    end
    F, a = finite_field(p)
    e = embed(F, L)
    return e(gen(F))
  end
end

@doc raw"""
    is_ordinary(E::EllCrv{T}) where T <: FinFieldElem
Return true when the elliptic curve is ordinary, i.e. not supersingular.
"""
function is_ordinary(E::EllCrv{T}) where T <: FinFieldElem
  return !is_supersingular(E)
end

#Following Identifying supersingular elliptic curves - Andrew V. Sutherland
@doc raw"""
    is_probable_supersingular(E::EllCrv{T}) where T <: FinFieldElem
Uses a probabilistic algorithm to test whether E is supersingular or not.
If the function returns false, the curve is proven to be ordinary.
If the function returns true, there is a high chance the curve is supersingular,
but the result hasn't been proven.
"""
function is_probable_supersingular(E::EllCrv{T}) where T <: FinFieldElem
  j = j_invariant(E)
  K = base_field(E)
  p = characteristic(K)

  local degj::Int

  if degree(K) == 1
    degj = 1
  else
    degj = degree(minpoly(j))
  end

  if degj == 1
    return monte_carlo_test(E, p+1)
  elseif degj == 2
    return monte_carlo_test(E, p+1) || monte_carlo_test(E, p-1)
  else
    return false
  end
end

function monte_carlo_test(E, n)
  E_O = infinity(E)

  for i in (1:10)
    P = rand(E)
    if n*P != E_O
      return false
    end
  end

  return true
end

# Inspired from Sage implementation in ell_finite_field.py
@doc raw"""
    supersingular_polynomial(p::IntegerUnion)
Return the polynomial whose roots correspond to j-invariants
of supersingular elliptic curves of characteristic p.
"""
function supersingular_polynomial(p::IntegerUnion)
  p = ZZRingElem(p)
  K = GF(p)
  KJ, J = polynomial_ring(GF(p), "J")
  if p < 3
    return J
  end

  m = divexact((p-1), 2)
  KXT, (X, T) = polynomial_ring(K, ["X", "T"])
  H = sum([binomial(m, i)^2 *T^i for i in (0:m)])
  F = T^2 * (T - 1)^2 * X - 256 * (T^2 - T + 1)^3
  R = resultant(F, H, 2)
  factors = factor(evaluate(R, [J, zero(KJ)]))
  S = elem_type(KJ)[f for (f, e) in factors]
  R = prod(S; init = one(KJ))
  return R
end

################################################################################
#
#  Group structure
#
################################################################################

# return (m, d) and (P, Q) such that d divides m, P, Q generate E(K),
# P has order m = lcm(d, m) = exp(E(K)), and
# E(K) = Z/d x Z/m.
#
# If m = 1, return [1], []
# If m != 1, d = 1, return [m], [P] (cyclic)
# If m != 1, d != 1, return [m, d], [P, Q]
#
# Not that Q does not necessarily has order d, nor that
# E(K) = <P> x <Q>
#
# Algorithm 2 from
# "The Weil Pairing, and Its Efficient Calculation", Victor S. Miller
# J. Cryptology (2004) 17: 235–261
# DOI: 10.1007/s00145-004-0315-8
#
#
@attr Tuple{Vector{fmpz}, Vector{EllCrvPt{T}}} function _grp_struct_with_gens(E::EllCrv{T}) where {T <: FinFieldElem}
  N = order(E)
  K = base_field(E)
  # TODO:
  # we do not have a multiplicative_order for field elements, so go
  # via disc_log :(
  A, AtoK = unit_group(K)
  f = _order_factored(E)

  if is_one(order(E))
    return ZZRingElem[], elem_type(E)[]
  end

  while true
    P, Q = rand(E), rand(E)
    s = _order_elem_via_fac(P)
    t = _order_elem_via_fac(Q)
    m = lcm(s, t)
    zeta = weil_pairing(P, Q, Int(m))
    d = order(AtoK\(zeta))
    if m*d == N
      if s != m && t != m
        continue
      end

      if t == m
        P, Q = Q, P
      end

      @assert Hecke._order_elem_via_fac(P) == m

      if is_one(m)
        return [m], typeof(P)[]
      elseif is_one(d)
        return [m], [P]
      else
        return [m, d], [P, Q]
      end
    end
  end
end

@doc raw"""
    gens(E::EllCrv{<:FinFieldElem}) -> Vector{EllCrvPt}

Return a list of generators of the group of rational points on $E$.

# Examples

```jldoctest; filter = r"Point.*"
julia> E = elliptic_curve(GF(101, 2), [1, 2]);

julia> gens(E)
2-element Vector{EllCrvPt{fqPolyRepFieldElem}}:
 Point  (93*o + 10 : 22*o + 69 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2
 Point  (89*o + 62 : 14*o + 26 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2

julia> E = elliptic_curve(GF(101), [1, 2]);

julia> gens(E)
1-element Vector{EllCrvPt{fpFieldElem}}:
 Point  (50 : 69 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2
```
"""
function gens(E::EllCrv{T}) where {T <: FinFieldElem}
  return _grp_struct_with_gens(E)[2]
end

@doc raw"""
    abelian_group(E::EllCrv{<:FinFieldElem}) -> GrpAbFinGen, Map

Return an abelian group $A$ isomorphic to the group of rational points of $E$
and a map $E \to A$.

!!! warning
    The map is not implemented yet.

```jldoctest
julia> E = elliptic_curve(GF(101, 2), [1, 2]);

julia> A, _ = abelian_group(E);

julia> A
GrpAb: Z/2 x Z/5200
```
"""
function abelian_group(E::EllCrv{U}) where {U <: FinFieldElem}
  _invdiv, _gens = _grp_struct_with_gens(E)
  if length(_gens) == 0
    strct = fmpz[]
    gens = elem_type(E)[]
  elseif length(_gens) == 1
    strct = copy(_invdiv)
    gens = _gens[1]
  elseif length(_gens) == 2
    P, Q = _gens
    # P generates a cyclic group of maximal order.
    # We change Q to Q - l*P, to make it not intersect
    # <P> (and still have the correct order)
    n1, n2 = _invdiv
    n = order(E)
    @assert Hecke._order_elem_via_fac(P) == n1
    @assert n2 == divexact(n, n1)
    _, k = ppio(n1, n2)
    Q = k * Q
    nQ = n2 * _order_elem_via_fac(n2 * Q) # could use that n2 * Q is killed by n1/k/n2
    S = divexact(n, nQ) * P
    T = n2 * Q
    x = disc_log(S, T, divexact(nQ, n2))
    Q = Q - x * divexact(n1, nQ) * P
    @assert _order_elem_via_fac(Q) == n2
    gens = Q, P
    strct = [n2, n1]
  end
  dlog = function(Q)
    error("Not implemented yet")
  end
  return abelian_group(strct), dlog
end

################################################################################
#
#  Discrete logarithm
#
################################################################################

# Just piggy back on the generic one

@doc raw"""
    disc_log(P::EllCrvPt, Q::EllCrvPt, [n::IntegerUnion]) -> ZZRingElem

Return the discrete logarithm $m$ of $Q$ with respect to the base $P$, that is,
$mP = Q$.

If a multiple $n$ of the order of $P$ is known, this can be supplied as an optional
argument.

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> P = E([6, 74])
Point  (6 : 74 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2

julia> Q = E([85, 43])
Point  (85 : 43 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2

julia> disc_log(P, Q)
13
```
"""
function disc_log(P::EllCrvPt, Q::EllCrvPt)
  @req parent(P) === parent(Q) "Points must lie on the same elliptic curve"
  n = _order_elem_via_fac(P)
  return disc_log(P, Q, n)
end

# n must be a multiple of the order of P
function disc_log(P::EllCrvPt{T}, Q::EllCrvPt{T}, n::IntegerUnion) where {T <: FinFieldElem}
  @req parent(P) === parent(Q) "Points must lie on the same elliptic curve"
  return disc_log_ph(P, Q, n, 1, (x, y) -> x + y, x -> -x, (x, n) -> n*x)
end
