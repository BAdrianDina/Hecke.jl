################################################################################
#
#  Contained in the alternating group
#
################################################################################

function is_discriminant_square(IdG::Main.ForeignGAP.MPtr)
  G = GAP.Globals.SmallGroup(IdG)
  mp = GAP.Globals.RegularActionHomomorphism(G)
  S = GAP.Globals.ImagesSource(mp)
  lg = GAP.Globals.GeneratorsOfGroup(S)
  for i = 1:length(lg)
    s = GAP.Globals.SignPerm(lg[i])
    if !isone(s)
      return false
    end
  end
  return true
end

################################################################################
#
#  Ramification at infinite places
#
################################################################################

function _real_level(L::Main.ForeignGAP.MPtr)
  #I compute the index of the first derived subgroup containing all the elements of order 2
  #First, I compute the subgroup generated by them.
  lElem = Main.ForeignGAP.MPtr[]
  G = L[1]
  ElemsG = GAP.Globals.Elements(G)
  for i = 1:length(ElemsG)
    g = ElemsG[i] 
    if GAP.Globals.Order(g) == 2
      push!(lElem, g)
    end 
  end
  S = GAP.Globals.Subgroup(G, GAP.julia_to_gap(lElem))
  #Now, I check containment.
  k = 0
  for i = 2:length(L)
    k += 1
    if !GAP.Globals.IsSubgroup(L[i], S)
      break
    end
  end
  return k
end


###############################################################################
#
#  Abelian extensions of QQ
#
###############################################################################

function abelian_extensionsQQ(gtype::Array{Int, 1}, bound::fmpz, only_real::Bool = false)
  
  gtype = map(Int, snf(DiagonalGroup(gtype))[1].snf)
  #Easy case: quadratic and biquadratic extensions
  if gtype == [2]
    lq = Hecke._quad_ext(Int(bound), only_real)
    res = Vector{FieldsTower}(undef, length(lq))
    for i = 1:length(lq)
      x = lq[i]
      E = EquationOrder(x[1])
      E.ismaximal = 1
      E.index = fmpz(1)
      E.gen_index = fmpq(1)
      E.disc = discriminant(E)
      Hecke._set_maximal_order(x[1], E)
      auts = Vector{NfToNfMor}(undef, 2)
      auts[1] = NfToNfMor(x[1], x[1], gen(x[1]))
      auts[2] = x[2][1]
      Hecke._set_automorphisms_nf(x[1], auts)
      res[i] = FieldsTower(x[1], x[2], x[3])
    end
    return res
  end
  if gtype == [2,2]
    l = Hecke._C22_exts_abexts(Int(bound), only_real)
    @vprint :Fields 1 "Computing maximal orders\n"
    @vprint :FieldsNonFancy 1 "Computing maximal orders\n"
    lf = Hecke._C22_with_max_ord(l)
    res1 = Vector{FieldsTower}(undef, length(lf))
    for i = 1:length(lf)
      res1[i] = FieldsTower(lf[i][1], lf[i][2], lf[i][3])
    end
    return res1
  end
  l1 = _abelian_extensionsQQ(gtype, bound, only_real)
  list1 = Vector{FieldsTower}(undef, length(l1))
  @vprint :Fields 1 "Computing maximal orders\n\n"
  @vprint :FieldsNonFancy 1 "Computing maximal orders\n"
  for i = 1:length(l1)
    @vprint :Fields 1 "\e[1FComputing maximal order $(i) /$(length(l1)) \n"
    x = l1[i]
    K, auts = Hecke._from_relative_to_absQQ(x[1], x[2])
    if length(gtype) == 1
      #If the group is cyclic, I prefer to have a generator!
      new_auts = Vector{NfToNfMor}(undef, 1)
      new_auts[1] = auts[1]
      for i = 2:length(auts)
        new_auts[1] *= auts[i]
      end
      list1[i] = FieldsTower(K, new_auts, [Hecke.NfToNfMor(base_field(x[1]), K, K(1))])
    else
      list1[i] = FieldsTower(K, auts, [Hecke.NfToNfMor(base_field(x[1]), K, K(1))])
    end
  end
  @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  return list1
  
end

function _abelian_extensionsQQ(gtype::Array{Int,1}, absolute_discriminant_bound::fmpz, only_real::Bool = false)
    
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  K, _ = NumberField(x-1, "a", cached = false)
  O = maximal_order(K)
  n = prod(gtype)
  expo = lcm(gtype)
    
  #Getting conductors
  l_conductors = Hecke.conductorsQQ(O, gtype, absolute_discriminant_bound)
  sort!(l_conductors, rev = true)
  len = length(l_conductors)
  @vprint :Fields 1 "Number of conductors: $(len) \n\n"
  @vprint :FieldsNonFancy 1 "Number of conductors: $(len) \n"
  
  
  complex = iseven(expo) && !only_real
  
  #Now, the big loop
  class_fields = Vector{Hecke.ClassField{MapRayClassGrp, GrpAbFinGenMap}}()
  for (i, k) in enumerate(l_conductors)
    if iszero(mod(i, 1000)) 
      pt = len - i
      @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol()) Conductors to test: $(pt)\n"
    end
    r, mr = Hecke.ray_class_groupQQ(O, k, complex, expo)
    if !Hecke._are_there_subs(r, gtype)
      continue
    end
    ls = subgroups(r, quotype = gtype, fun = (x, y) -> quo(x, y, false)[2])
    for s in ls
      C = ray_class_field(mr, s)::ClassField{MapRayClassGrp, GrpAbFinGenMap}
      if Hecke._is_conductor_minQQ(C, n) && Hecke.discriminant_conductorQQ(O, C, k, absolute_discriminant_bound, n)
        push!(class_fields, C)
      end
    end
  end
  fields = Vector{Tuple{Hecke.NfRelNS{nf_elem}, Array{Hecke.NfRelNSToNfRelNSMor{nf_elem},1}}}(undef, length(class_fields))
  for i = 1:length(class_fields)
    @vprint :Fields 1 "\e[1FComputing class field $(i) /$(length(class_fields)) \n"
    C = class_fields[i]
    fields[i] = (number_field(C), Hecke.automorphism_groupQQ(C))
  end
  @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Number of fields found: $(length(fields)) \n"
  @vprint :FieldsNonFancy 1 "Number of fields found: $(length(fields)) \n"
  return fields

end

###############################################################################
#
#  General abelian layer
#
###############################################################################

function check_ext(C::Hecke.ClassField, bound::fmpz, Dcond::Dict, Ddisc::Dict)

  @vtime :Fields 3 fl2 = Hecke._is_conductor_min_normal(C, lwp = Dcond)
  if !fl2
    return false
  end
  @vtime :Fields 3 fl3 = Hecke.discriminant_conductor(C, bound, lwp = Ddisc) 
  if !fl3
    return false
  end
  return true
  
end

function _construct_grp(IdH::Main.ForeignGAP.MPtr, uncom::Int)
  G = GAP.Globals.SmallGroup(IdH)
  L = GAP.Globals.DerivedSeries(G)
  mH1 = GAP.Globals.NaturalHomomorphismByNormalSubgroup(G, L[end-1])
  K = GAP.Globals.Kernel(mH1)
  gens = GAP.gap_to_julia(GAP.Globals.MinimalGeneratingSet(K))
  for i = 1:length(gens)
    o = GAP.Globals.Order(gens[i])
    ex = ppio(o, uncom)[1]
    gens[i] = gens[i]^ex 
  end
  S = GAP.Globals.Subgroup(G, GAP.julia_to_gap(gens))
  Q = GAP.Globals.FactorGroup(G, S)
  IdCheck = GAP.Globals.IdGroup(Q)
  return IdCheck
end

function max_ramified_prime(O::NfOrd, gtype::Vector{Int}, bound::fmpz)
  n = prod(gtype)
  fac = factor(n)
  m = Int(maximum(keys(fac.fac)))
  k = divexact(n, m)
  b1 = Int(root(bound, degree(O)*(m-1)*k)) 
  return b1
end

function _abelian_normal_extensions(F::FieldsTower, gtype::Array{Int, 1}, absbound::fmpz, IdCheck::Main.ForeignGAP.MPtr, only_real::Bool, IdG::Main.ForeignGAP.MPtr)
  K = F.field
  O = maximal_order(K) 
  n = prod(gtype)
  inf_plc = Array{InfPlc, 1}()
  if abs(discriminant(O))^n > absbound
    return Vector{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}}[]
  end
  bound = div(absbound, abs(discriminant(O))^n)
  l_conductors = conductors_with_restrictions(F, gtype, IdG, bound)
  @vprint :Fields 1 "   Number of conductors: $(length(l_conductors))\n"
  @vprint :FieldsNonFancy 1 "Number of conductors: $(length(l_conductors))\n"
  if length(l_conductors) == 0
    @vprint :Fields 1 "\n"
    return Vector{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}}[]
  end
  @vprint :Fields 2 "\n"
  @vprint :Fields 1 "Computing class group"
  @vtime :Fields 2 Cl, mCl = class_group(O, use_aut = true)
  @vprint :Fields 1 "$(Hecke.clear_to_eol())"
  if mod(n, 2) == 0 && !only_real
    inf_plc = real_places(K)
  end
  expo = lcm(gtype)
  if length(l_conductors) == 1 && isone(l_conductors[1][1]) && isempty(l_conductors[1][2]) && !divisible(order(Cl)* (2^length(inf_plc)), fmpz(n))
    @vprint :Fields 1 "\n"
    return Vector{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}}[]
  end
  Hecke.allow_cache!(mCl)
  @vtime :Fields 3 rcg_ctx = Hecke.rayclassgrp_ctx(O, expo)
  @vprint :Fields 1 "\n"
  j = -1
  first_group = true
  autos = F.generators_of_automorphisms
  class_fields_with_act = Tuple{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}, Vector{GrpAbFinGenMap}}[]
  for k in l_conductors
    j += 1
    @vprint :Fields 1 "\e[1FConductors to test: $(length(l_conductors)-j) \n"
    @vprint :Fields 3 "\n\n"
    @vtime :Fields 3 r, mr = Hecke.ray_class_group_quo(O, k[1], k[2], inf_plc, rcg_ctx)
    if !Hecke._are_there_subs(r, gtype)
      continue
    end
    if first_group
      B1 = maximum([next_prime(max_ramified_prime(O, gtype, bound)), 211])
      lP = Hecke.find_gens(pseudo_inv(rcg_ctx.class_group_map), PrimesSet(B1, -1))[1]
      rcg_ctx.class_group_map.small_gens = lP
      first_group = false
    end
    mr.clgrpmap.small_gens = rcg_ctx.class_group_map.small_gens
    @vtime :Fields 3 act = Hecke.induce_action(mr, autos)
    @vtime :Fields 3 ls = stable_subgroups(r, act, op = (x, y) -> quo(x, y, false)[2], quotype = gtype)
    Dcond = Dict{Int, Array{GrpAbFinGenElem, 1}}()
    Ddisc = Dict{Tuple{Int, Int}, Array{GrpAbFinGenElem, 1}}()
    for s in ls
      @hassert :Fields 1 order(codomain(s)) == n
      C = ray_class_field(mr, s)
      fl = check_ext(C, bound, Dcond, Ddisc)
      if fl
        res_act = _action(s, act)
        @vtime :Fields 3 fl1 = check_group_extension(IdCheck, autos, res_act)
        if fl1
          push!(class_fields_with_act, (C, res_act))
        end
      end
    end
    @vprint :Fields 3 "\n\n"
  end 
  if isempty(class_fields_with_act)
    return Vector{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}}[]
  end
  emb_sub = F.subfields[end]
  @vprint :Fields 1 "\e[1F$(Hecke.clear_to_eol())Sieving $(length(class_fields_with_act)) abelian extensions\n"
  class_fields = Hecke.check_abelian_extensions(class_fields_with_act, autos, emb_sub)
  return class_fields
end

################################################################################
#
#  From the class fields to the computation of the defining polynomials
#
################################################################################

function from_class_fields_to_fields(class_fields::Vector{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}}, autos::Vector{NfToNfMor}, grp_to_be_checked::Dict{Int, Main.ForeignGAP.MPtr})
  
  if isempty(class_fields)
    @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    return Tuple{Hecke.NfRelNS{nf_elem}, Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}}[] 
  end
  K = base_ring(class_fields[1])
  divisors_of_n = collect(keys(grp_to_be_checked))
  sort!(divisors_of_n)
  pclassfields = Vector{Vector{typeof(class_fields[1])}}(undef, length(divisors_of_n))
  right_grp = trues(length(class_fields))
  ind = 1
  for p in divisors_of_n
    it = findall(right_grp)
    if iszero(length(it))
      break
    end
    cfieldsp = Vector{typeof(class_fields[1])}(undef, length(class_fields))
    for i in it
      cfieldsp[i] = Hecke.maximal_p_subfield(class_fields[i], Int(p))
    end
    idE = grp_to_be_checked[p]
    if iszero(mod(order(torsion_unit_group(maximal_order(K))[1]), p^(valuation(exponent(class_fields[1]), p))))
      compute_fields(cfieldsp, autos, idE, right_grp)
      pclassfields[ind] = cfieldsp
      ind += 1
      continue
    end
    E = GAP.Globals.SmallGroup(idE)
    S, H, ab_inv = max_ab_norm_sub_containing(E)
    if S == H 
      compute_fields(cfieldsp, autos, idE, right_grp)
      pclassfields[ind] = cfieldsp
      ind += 1
      continue
    end
    @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    # I can compute the fields over a subfield.
    #First, I need the subfields.
    K = base_field(class_fields[1])
    assure_automorphisms(K, autos)
    subfields = compute_subfields(K, E, H, S)
    computing_over_subfields(cfieldsp, subfields, idE, autos, right_grp, ab_inv)
    pclassfields[ind] = cfieldsp
    ind += 1
  end
  it = findall(right_grp)
  fields = Vector{Tuple{NfRelNS{nf_elem}, Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}}}(undef, length(it))
  ind = 1
  for i in it
    res = Vector{typeof(class_fields[1])}(undef, length(divisors_of_n))
    for j = 1:length(divisors_of_n)
      res[j] = pclassfields[j][i]
    end
    fields[ind] = _ext_and_autos(res, autos)
    ind += 1
  end
  return fields
  
end

function compute_fields(class_fields::Vector{Hecke.ClassField{Hecke.MapRayClassGrp, GrpAbFinGenMap}}, autos::Vector{NfToNfMor}, grp_to_be_checked::Main.ForeignGAP.MPtr, right_grp)
  it = findall(right_grp)
  K = base_field(class_fields[it[1]])
  fields = Tuple{Hecke.NfRelNS{nf_elem}, Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}}[]
  expo = Int(exponent(codomain(class_fields[it[1]].quotientmap)))
  
  set_up_cycl_ext(K, expo, autos)
  @vprint :Fields 3 "Computing the fields directly\n"
  for i in it
    C = class_fields[i]
    L = NumberField(C)
    #L = NumberField_using_Brauer(C)
    autL = Hecke.absolute_automorphism_group(C, autos)
    if !isone(gcd(degree(K), expo)) 
      Cpperm = permutation_group(autL)
      if GAP.Globals.IdGroup(Cpperm) != grp_to_be_checked
        right_grp[i] = false
      end
    end
  end
  return right_grp
end

function _ext_and_autos(resul::Vector{Hecke.ClassField{S, T}}, autos::Vector{NfToNfMor}) where S where T
  if length(resul) == 1
    return resul[1].A, resul[1].AbsAutGrpA
  end
  K = domain(autos[1])
  pols = Generic.Poly{nf_elem}[]
  for i = 1:length(resul)
    append!(pols, [Hecke.isunivariate(resul[i].A.pol[w])[2] for w = 1:length(resul[i].A.pol)])
  end
  L, gL = number_field(pols, cached = false, check = false)
  autL = Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}()
  imgs_auts_base_field = Vector{Vector{Hecke.NfRelNSElem{nf_elem}}}(undef, length(autos))
  for i = 1:length(autos)
    imgs_auts_base_field[i] = gens(L)
  end
  #Now, the automorphisms...
  for i = 1:length(resul)
    Cp = resul[i]
    p = ispower(degree(Cp))[2]
    w = 1
    while mod(degree(pols[w]), p) != 0
      w += 1
    end 
    auts = Cp.AbsAutGrpA
    for phi in auts
      if phi.coeff_aut.prim_img == gen(K)
        imgsphi = gens(L)
        for ind = w:(w+length(Cp.A.pol)-1)
          imgsphi[ind] = evaluate(Hecke.isunivariate(phi.emb[ind-w+1].data)[2], imgsphi[ind])
        end
        push!(autL, Hecke.NfRelNSToNfRelNSMor(L, L, imgsphi))
      else
        ind_aut = 1
        while autos[ind_aut] != phi.coeff_aut
          ind_aut += 1
        end
        for ind = w:(w+length(Cp.A.pol)-1)
          imgs_auts_base_field[ind_aut][ind] = Hecke.msubst(phi.emb[ind-w+1].data, gL[w:(w+length(Cp.A.pol)-1)])
        end
      end
    end
  end
  for i = 1:length(imgs_auts_base_field)
    push!(autL, Hecke.NfRelNSToNfRelNSMor(L, L, autos[i], imgs_auts_base_field[i]))
  end
  return L, autL

end

function set_up_cycl_ext(K::AnticNumberField, n::Int, autK::Array{NfToNfMor, 1})
  fac = factor(n)
  for (p, v) in fac
    e = Int(p)^v
    if e == 2
      continue
    end
    C = cyclotomic_extension(K, e)
    if degree(C.Kr) == 1
      continue
    end
    auts = automorphisms(C, gens = autK, copy = false)
    @vprint :Fields 1 ": computing class group of cyclotomic extension of order $e"
    @vprint :FieldsNonFancy 1 "computing class group of cyclotomic extension of order $e\n"
    Cl, mCl = class_group(maximal_order(C.Ka), use_aut = true)
    Hecke.allow_cache!(mCl)
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  end
  return nothing

end

function _action(t::Hecke.GrpAbFinGenMap, act::Array{Hecke.GrpAbFinGenMap,1})
  
  T = codomain(t)
  S, mS= snf(T)
  new_act = Array{Hecke.GrpAbFinGenMap, 1}(undef, length(act))
  for i = 1:length(act)
    res = mS.map*act[i].map*mS.imap
    new_act[i] = Hecke.GrpAbFinGenMap(S, S, res)
  end
  return new_act
  
end

################################################################################
#
#  Maximal subgroups which is in direct product with the derived subgroup
#
################################################################################

function max_ab_norm_sub_containing(G::Main.ForeignGAP.MPtr)
  
  D = GAP.Globals.DerivedSeries(G)
  H = D[end-1]
  G1 = GAP.Globals.Centralizer(G, H)
  if G1 == H
    return H, H, Int[]
  end
  #First, I check if the centralizer split directly as a direct product.
  sc = GAP.Globals.ComplementClassesRepresentatives(G1, H)
  if !GAP.Globals.IsEmpty(sc)
    return G1, H, GAP.gap_to_julia(Vector{Int}, GAP.Globals.AbelianInvariants(sc[1]))
  end
  lS = GAP.gap_to_julia(GAP.Globals.ConjugacyClassesSubgroups(G1))
  #TODO: Subgroups in the quotient by H and not in the full group
  candidate = H
  sizecandidate = GAP.Globals.Size(H)
  ab_invariants = GAP.gap_to_julia(Vector{Int}, GAP.Globals.AbelianInvariants(H))
  for S in lS
    s = GAP.Globals.Representative(S)
    if !GAP.Globals.IsSubset(s, H)
      continue
    end
    sc = GAP.Globals.ComplementClassesRepresentatives(s, H)
    if GAP.Globals.IsEmpty(sc)
      continue
    end
    sncandidate = GAP.Globals.Size(s)
    if sncandidate > sizecandidate
      candidate = s
      sizecandidate = sncandidate
      ab_invariants = GAP.gap_to_julia(Vector{Int}, GAP.Globals.AbelianInvariants(sc[1]))
    end
  end
  return candidate, H, ab_invariants
end

################################################################################
#
#  Computing the extension over subfields
#
################################################################################

function computing_over_subfields(class_fields, subfields, idE, autos, right_grp, ab_invariants::Vector{Int})

  it = findall(right_grp)
  new_class_fields, subs, to_be_done = translate_class_field_down(subfields, class_fields, it, ab_invariants)
  for x in to_be_done
    C = class_fields[x]
    L = number_field(C)
    auts = absolute_automorphism_group(C, autos)
    Cpperm = permutation_group(auts)
    if GAP.Globals.IdGroup(Cpperm) == idE
      error("Something went wrong")
    end
    right_grp[x] = false
  end
  it = findall(right_grp)
  if isempty(it)
    return Vector{Tuple{Hecke.NfRelNS{nf_elem}, Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}}}()
  end
  translate_fields_up(class_fields, new_class_fields, subs, it)
  #Now, finally, the automorphisms computation and the isomorphism check
  for i in it
    C = class_fields[i]
    C1 = new_class_fields[i]
    mL = subs[1]
    indsubf = 1
    while domain(mL) != base_field(C1)
      indsubf += 1
      mL = subs[indsubf]
    end
    maprel = Hecke.NfRelNSToNfRelNSMor(C1.A, C.A, mL, gens(C.A))
    autsrelC1 = Hecke.rel_auto(C1)
    autsrelC = Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}(undef, length(autsrelC1))
    for s = 1:length(autsrelC1)
      el = autsrelC1[s]
      autsrelC[s] = Hecke.NfRelNSToNfRelNSMor(C.A, C.A, [maprel(x) for x in el.emb])
      @hassert :Fields 1 isconsistent(autsrelC[s])
    end
    rel_extend = Hecke.new_extend_aut(C, autos)
    autsA = vcat(rel_extend, autsrelC)
    C.AbsAutGrpA = autsA
    if !iscoprime(degree(C), degree(base_field(C)))
      Cpperm = permutation_group(autsA)
      if GAP.Globals.IdGroup(Cpperm) != idE
        right_grp[i] = false
      end
    end
  end
  it = findall(right_grp)
  fields = Vector{Tuple{Hecke.NfRelNS{nf_elem}, Vector{Hecke.NfRelNSToNfRelNSMor{nf_elem}}}}(undef, length(it))
  ind = 1
  for i in it
    C = class_fields[i]
    fields[ind] = (C.A, C.AbsAutGrpA)
    ind += 1
  end
  return fields 
end


function translate_extensions(mL::NfToNfMor, class_fields, new_class_fields, ctxK, it, ab_invariants::Vector{Int})
  to_be_done = Int[]
  L = domain(mL)
  OL = maximal_order(L)
  K = codomain(mL)
  OK = maximal_order(K)
  n = Int(exponent(codomain(class_fields[it[1]].quotientmap)))
  ordext = Int(order(codomain(class_fields[it[1]].quotientmap)))
  ctx = Hecke.rayclassgrp_ctx(OL, n)
  d = divexact(discriminant(maximal_order(K)), discriminant(OL)^(divexact(degree(K), degree(L))))
  f = factor(ideal(OL, d))
  F = factor(ideal(OK, d))
  ab_invariants_mod = map(x -> mod(x, n), ab_invariants)
  for indclf in it
    if isassigned(new_class_fields, indclf)
      continue
    end
    C = class_fields[indclf]
    #First, I need a modulus.
    #I take the intersection of the modulus of C with L
    mR = C.rayclassgroupmap
    fM0 = copy(mR.fact_mod)
    fm0 = Dict{NfOrdIdl, Int}()
    for (p, v) in fM0
      p1 = Hecke.intersect_prime(mL, p)
      if !haskey(fm0, p1)
        if iscoprime(minimum(p1, copy = false), n) 
          fm0[p1] = 1
        else
          fm0[p1] = v
        end
      end
      ep = divexact(ramification_index(p), ramification_index(p1))
      fM0[p] = ep*v
    end
    #Now, I have problems, so I need to add the ramification of the other extension.
    for (p, v) in f
      if !haskey(fm0, p)
        if isone(gcd(minimum(p), n)) 
          fm0[p] = 1
        else
          fm0[p] = v
        end
      else
        if !isone(gcd(minimum(p), n)) 
          fm0[p] = max(v, fm0[p]) 
        end
      end
      lPP = prime_decomposition(mL, p)
      for (P, vP) in lPP
        if haskey(fM0, P)
          fM0[P] = max(fM0[P], 2*vP*fm0[p])
        else
          fM0[P] = vP*fm0[p]*2
        end
      end
    end
    infplc = InfPlc[]
    if iszero(mod(n, 2)) 
      infplc = real_places(L)
    end
    @vprint :Fields 3 "Checking if I can compute $(indclf) over a subfield\n\n "
    @vtime :Fields 3 r, mr = Hecke.ray_class_group_quo(OL, fm0, infplc, ctx, check = false)
    if exponent(r) < n || order(r) < degree(C)
      push!(to_be_done, indclf)
      continue
    end 
    #Now, the norm group of K over L
    
    @vtime :Fields 3 ngL, mngL = Hecke.norm_group(mL, mr, prod(ab_invariants_mod))
    @hassert :Fields 1 divisible(divexact(fmpz(degree(codomain(mL))), degree(domain(mL))), divexact(order(r), order(ngL))) 
    if !divisible(order(ngL), degree(C)) || !divisible(exponent(C), n)
      push!(to_be_done, indclf)
      continue
    end
    #Finally, the norm group of C over L
    #I use the usual strategy, as in check_abelian_extension
    for (p, v) in F
      if iscoprime(minimum(p, copy = false), degree(C))
        fM0[p] = 1
      else
        if haskey(fM0, p)
          fM0[p] = max(v, fM0[p])
        else
          fM0[p] = v
        end 
      end
    end
    inf_plc2 = InfPlc[]
    if !isempty(infplc)
      inf_plc2 = real_places(K)
    end
    @vtime :Fields 3 RM, mRM = Hecke.ray_class_group_quo(OK, fM0, inf_plc2, ctxK, check = false)
    if !isdefined(ctxK.class_group_map, :small_gens)
      ctxK.class_group_map.small_gens = find_gens(pseudo_inv(ctxK.class_group_map), PrimesSet(101, -1))[1]
    end
    @vtime :Fields 3 lP, gS = Hecke.find_gens(mRM)
    listn = NfOrdIdl[norm(mL, x) for x in lP]
    # Create the map between R and r by taking norms
    preimgs = Vector{GrpAbFinGenElem}(undef, length(listn))
    for i = 1:length(preimgs)
      preimgs[i] = mr\listn[i]
    end
    proj = hom(gS, preimgs)
    #compute the norm group of C in RM
    prms = Vector{GrpAbFinGenElem}(undef, length(lP))
    for i = 1:length(lP)
      prms[i] = C.quotientmap(mR\lP[i])
    end
    RMtoR = hom(gS, prms)
    k, mk = kernel(RMtoR)
    @hassert :Fields 1 isisomorphic(cokernel(mk)[1], codomain(C.quotientmap))
    mp = mk*proj
    ck, mck = cokernel(mp)
    #If everything could work, then ck should be the direct product of the abelian extension I am searching for and 
    #the maximal abelian subextension of K/L
    G1 = snf(cokernel(mngL)[1])[1]
    G2 = snf(codomain(C.quotientmap))[1]
    if !_are_there_subs(ck, map(Int, vcat(G1.snf, G2.snf)))
      push!(to_be_done, indclf)
      continue
    end
    @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Doing field $(indclf) / $(length(class_fields))"
    s, ms = image(mngL*mck)#sub(ck, GrpAbFinGenElem[mck(mngL(x)) for x in gens(ngL)])
    mq1 = find_complement(ms)
    mqq = mck * mq1 
    @hassert :Fields 1 domain(mqq) == r
    C1 = ray_class_field(mr, mqq)
    number_field(C1)
    @hassert :Fields 1 degree(C1) == degree(C)
    new_class_fields[indclf] = C1
  end
  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  return to_be_done
  
end

function divisible(x::Integer, y::Integer)
  return divisible(fmpz(x), fmpz(y))
end


#m is the injection representing a subgroup
#we want a complement of m 
function find_complement(m::GrpAbFinGenMap)
  q, mq = cokernel(m)
  s, ms = snf(q)
  cmpl = GrpAbFinGenElem[]
  for x in gens(s)
    push!(cmpl, mq\(ms(x)))
  end
  return quo(codomain(m), cmpl, false)[2]
end

mutable struct BadField <: Exception
  K
end

function Base.show(io::IO, E::BadField)
  if isdefined(E, :K)
    println("Bad field $(K) encountered")
  else
    println("Bad field encountered")
  end
end


function create_sub(ss, iso, PermGAP, auts, K)
  lS = GAP.Globals.MinimalGeneratingSet(ss)
  lS1 = Main.ForeignGAP.MPtr[GAP.Globals.Image(iso, lS[i]) for i in 1:length(lS)]
  inds = Vector{Int}(undef, length(lS1))
  for j = 1:length(inds)
    el = lS1[j]
    inds[j] = findfirst(x -> x == el, PermGAP)
  end
  mL = Hecke.fixed_field(K, NfToNfMor[auts[i] for i in inds])[2]
  return mL
end

function compute_subfields(K::AnticNumberField, E, H, S)
  
  proj = GAP.Globals.NaturalHomomorphismByNormalSubgroup(E, H)
  Hn = GAP.Globals.ImagesSource(proj)
  imgsS = GAP.Globals.Image(proj, S)
  autsHn = GAP.Globals.Elements(GAP.Globals.AutomorphismGroup(Hn))
  orbitS = [imgsS]
  for i = 1:length(autsHn)
    varphi = autsHn[i]
    Sn = GAP.Globals.Image(varphi, imgsS)
    if !(Sn in orbitS)
      push!(orbitS, Sn)
    end 
  end
  auts = automorphisms(K, copy = false)
  Hperm = _from_autos_to_perm(auts)
  Hauts = _perm_to_gap_grp(Hperm)
  PermGAP = Vector{Main.ForeignGAP.MPtr}(undef, length(Hperm))
  for w = 1:length(Hperm)
    PermGAP[w] = _perm_to_gap_perm(Hperm[w])
  end
  iso = GAP.Globals.IsomorphismGroups(Hn, Hauts)
  return (create_sub(ss, iso, PermGAP, auts, K) for ss in orbitS)

end

function translate_class_field_down(subfields, class_fields, it, ab_invariants)
  new_class_fields = similar(class_fields)
  #Now, I translate the fields over the subfields.
  to_be_done = Int[i for i in it]
  created_subfields = NfToNfMor[]
  K = base_field(class_fields[to_be_done[1]])
  OK = maximal_order(K)
  ctxK = Hecke.rayclassgrp_ctx(OK, exponent(class_fields[to_be_done[1]]))
  for mL in subfields
    push!(created_subfields, mL)
    to_be_done_new = translate_extensions(mL, class_fields, new_class_fields, ctxK, it, ab_invariants)
    if length(to_be_done_new) == 0 
      return new_class_fields, created_subfields, to_be_done_new
    end
    to_be_done = to_be_done_new
  end
  return new_class_fields, created_subfields, to_be_done
end


function translate_fields_up(class_fields, new_class_fields, subfields, it)
  K = base_field(class_fields[it[1]])
  Ky = PolynomialRing(K, "y", cached = false)[1]
  for i in it
    C = class_fields[i]
    C1 = new_class_fields[i]
    mL = subfields[1]
    indsubf = 1
    while domain(mL) != base_field(C1)
      indsubf += 1
      mL = subfields[indsubf]
    end
    L = domain(mL)
    D = Dict{Int, NfToNfMor}()
    for j = 1:length(new_class_fields[i].cyc)
      d = degree(new_class_fields[i].cyc[j])
      if !haskey(D, d)
        CEK = cyclotomic_extension(K, d)
        CEL = cyclotomic_extension(L, d)
        img = gen(CEK.Kr)
        if degree(CEK.Kr) != euler_phi(d)
          pp = map_coeffs(mL, CEL.Kr.pol, cached = false)
          while !iszero(pp(img))
            mul!(img, img, gen(CEK.Kr))
          end
        end
        mrel = Hecke.NfRelToNfRelMor(CEL.Kr, CEK.Kr, mL, img) 
        @hassert :Fields 1 isconsistent(mrel)
        g = mrel(CEL.mp[1](gen(CEL.Ka)))
        mp = hom(CEL.Ka, CEK.Ka, CEK.mp[1]\(g), check = false)
        D[d] = mp
      end
    end
    cyc = Vector{Hecke.ClassField_pp{Hecke.MapRayClassGrp, GrpAbFinGenMap}}(undef, length(C1.cyc))
    for j = 1:length(cyc)
      Ccyc = C1.cyc[j]
      d = degree(Ccyc)
      #First, easy: the degree
      Cpp = Hecke.ClassField_pp{Hecke.MapRayClassGrp, GrpAbFinGenMap}()
      Cpp.rayclassgroupmap = C.rayclassgroupmap
      Cpp.degree = d
      #Then, the fac elem corresponding to the generator of the Kummer Extension
      Cpp.a = FacElem(Dict{nf_elem, fmpz}(D[d](x) => v for (x, v) in Ccyc.a))
      #Now, the Kummer extension
      Lzeta = codomain(D[d])
      Lt = PolynomialRing(Lzeta, "t", cached = false)[1]
      d1 = degree(Ccyc.K)
      coeffs = Vector{nf_elem}(undef, d1 + 1)
      coeffs[1] = D[d](coeff(Ccyc.K.pol, 0))
      for s = 2:length(coeffs)-1
        coeffs[s] = zero(Lzeta)
      end
      coeffs[end] = one(Lzeta)
      Cpp.K = number_field(Lt(coeffs), cached = false, check = false)[1]
      #The target extension
      fdef = map_coeffs(mL, Ccyc.A.pol, parent = Ky, cached = false)
      Cpp.A = number_field(fdef, cached = false, check = false)[1]
      #Now, the primitive element of the target extension seen in Cpp.K
      mrel2 = Hecke.NfRelToNfRelMor(Ccyc.K, Cpp.K, D[d], gen(Cpp.K))
      @hassert :Fields 1 isconsistent(mrel2)
      @hassert :Fields 1 parent(Ccyc.pe) == domain(mrel2)
      Cpp.pe = mrel2(Ccyc.pe) 
      CEKK = cyclotomic_extension(K, d)
      @hassert :Fields 1 iszero(map_coeffs(CEKK.mp[2], fdef, cached = false)(Cpp.pe))
      Cpp.o = d1
      cyc[j] = Cpp
    end
    C.cyc = cyc
    C.A = number_field([cyc[j].A.pol for j = 1:length(cyc)], cached = false, check = false)[1]
  end
  return nothing

end
