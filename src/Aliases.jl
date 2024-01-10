import Nemo: is_cyclo_type
import Nemo: is_embedded
import Nemo: is_maxreal_type
import Nemo: ZZModRing  # FIXME: remove if/once Nemo exports this
include(joinpath(pathof(Nemo), "..", "Aliases.jl"))

# make some Julia names compatible with our naming conventions
@alias is_hermitian ishermitian

# for backwards compatibility
@alias AbsLat AbstractLat
@alias AbsSpace AbstractSpace
@alias AbsSpaceMor AbstractSpaceMor
@alias add_assert_scope add_assertion_scope
@alias add_verbose_scope add_verbosity_scope

@alias get_assert_level get_assertion_level
@alias get_verbose_level get_verbosity_level
@alias genera integer_genera
@alias genera_hermitian hermitian_genera
@alias genera_quadratic quadratic_genera
@alias GenusHerm HermGenus
@alias GenusQuad QuadGenus

@alias hasalgebra has_algebra
@alias hasembedding has_embedding
@alias hasimage has_image
@alias hasmatrix_action has_matrix_action
@alias hasroot has_root

@alias is2_normal_difficult is_2_normal_difficult
@alias isGLZ_conjugate is_GLZ_conjugate
@alias isabelian is_abelian
@alias isabelian2 is_abelian2
@alias isabsolute is_absolute
@alias isabsolutely_primitive is_absolutely_primitive
@alias isalmost_maximally_ramified is_almost_maximally_ramified
@alias isautomorphisms_known is_automorphisms_known
@alias isbass is_bass
@alias isbijective is_bijective
@alias iscached is_cached
@alias iscanonical is_canonical
@alias iscentral is_central
@alias ischain_complex is_chain_complex
@alias ischaracteristic is_characteristic
@alias iscm is_cm
@alias iscm_field is_cm_field
@alias iscm_field_easy is_cm_field_easy
@alias iscm_field_known is_cm_field_known
@alias iscochain_complex is_cochain_complex
@alias iscommutative is_commutative
@alias iscommutative_known is_commutative_known
@alias iscomplex is_complex
@alias iscomplex_conjugation is_complex_conjugation
@alias isconductor is_conductor
@alias isconjugate is_conjugate
@alias isconsistent is_consistent
@alias iscontained is_contained
@alias iscoprime is_coprime
@alias iscyclic is_cyclic
@alias iscyclotomic_type is_cyclotomic_type
@alias isdefining_polynomial_nice is_defining_polynomial_nice
@alias isdefinite is_definite
@alias isdegenerate is_degenerate
@alias isdiagonalisable is_diagonalisable
@alias isdiscriminant is_discriminant
@alias isdivisible is_divisible
@alias isdivisible2 is_divisible2
@alias isdivisible_mod_ideal is_divisible_mod_ideal
@alias isdyadic is_dyadic
@alias iseichler is_eichler
@alias iseisenstein_polynomial is_eisenstein_polynomial
@alias iseq is_eq
@alias isequation_order is_equation_order
@alias isequivalent is_equivalent
@alias isequivalent_with_isometry is_equivalent_with_isometry
@alias isfinite_gen is_finite_gen
@alias isfinite_snf is_finite_snf
@alias isfixed_point_free is_fixed_point_free
@alias isfree is_free
@alias isfree_a4_fabi is_free_a4_fabi
@alias isfree_a5_fabi is_free_a5_fabi
@alias isfree_resolution is_free_resolution
@alias isfree_s4_fabi is_free_s4_fabi
@alias isfrom_db is_from_db
@alias isfull_lattice is_full_lattice
@alias isfundamental_discriminant is_fundamental_discriminant
@alias isgenus is_genus
@alias isgood_bong is_good_bong
@alias isgorenstein is_gorenstein
@alias isidentity is_identity
@alias isin is_in
@alias isindefinite is_indefinite
@alias isindependent is_independent
@alias isindex_divisor is_index_divisor
@alias isinduced is_induced
@alias isinert is_inert
@alias isinfinite is_infinite
@alias isinjective is_injective
@alias isintegral is_integral
@alias isinvolution is_involution
@alias isirreducible_easy is_irreducible_easy
@alias isirreducible_known is_irreducible_known
@alias isisometric is_isometric
@alias isisometric_with_isometry is_isometric_with_isometry
@alias isisotropic is_isotropic
@alias iskummer_extension is_kummer_extension
@alias isleaf is_leaf
@alias isleft_ideal is_left_ideal
@alias islessorequal is_lessorequal
@alias islinearly_disjoint is_linearly_disjoint
@alias islll_reduced is_lll_reduced
@alias islocal_norm is_local_norm
@alias islocal_square is_local_square
@alias islocally_equivalent is_locally_equivalent
@alias islocally_free is_locally_free
@alias islocally_hyperbolic is_locally_hyperbolic
@alias islocally_isometric is_locally_isometric
@alias islocally_isometric_kirschmer is_locally_isometric_kirschmer
@alias islocally_isomorphic is_locally_isomorphic
@alias islocally_isomorphic_with_isomophism is_locally_isomorphic_with_isomophism
@alias islocally_represented_by is_locally_represented_by
@alias ismaximal is_maximal
@alias ismaximal_integral is_maximal_integral
@alias ismaximal_known is_maximal_known
@alias ismaximal_known_and_maximal is_maximal_known_and_maximal
@alias ismaximal_order_known is_maximal_order_known
@alias ismodular is_modular
@alias isnegative_definite is_negative_definite
@alias isnorm is_norm
@alias isnorm_divisible is_norm_divisible
@alias isnorm_divisible_pp is_norm_divisible_pp
@alias isnorm_fac_elem is_norm_fac_elem
@alias isnormal is_normal
@alias isnormal_basis_generator is_normal_basis_generator
@alias isnormal_difficult is_normal_difficult
@alias isnormal_easy is_normal_easy
@alias isnormalized is_normalized
@alias isone_sided is_one_sided
@alias ispairwise_coprime is_pairwise_coprime
@alias ispositive_definite is_positive_definite
@alias ispower_trager is_power_trager
@alias ispower_unram is_power_unram
@alias isprimary is_primary
@alias isprime_known is_prime_known
@alias isprime_nice is_prime_nice
@alias isprime_power is_prime_power
@alias isprimitive is_primitive
@alias isprimitive_over is_primitive_over
@alias isprimitive_root is_primitive_root
@alias isprincipal is_principal
@alias isprincipal_fac_elem is_principal_fac_elem
#@alias isprincipal_maximal is_principal_maximal
#@alias isprincipal_maximal_fac_elem is_principal_maximal_fac_elem
#@alias isprincipal_non_maximal is_principal_non_maximal
@alias ispseudo_hnf is_pseudo_hnf
@alias isquadratic is_quadratic
@alias isquadratic_type is_quadratic_type
@alias isquaternion_algebra is_quaternion_algebra
@alias isradical_extension is_radical_extension
@alias isramified is_ramified
@alias isrationally_equivalent is_rationally_equivalent
@alias isrationally_isometric is_rationally_isometric
@alias isreduced is_reduced
@alias isreducible is_reducible
@alias isregular is_regular
@alias isregular_at is_regular_at
@alias isrepresented_by is_represented_by
@alias isright_ideal is_right_ideal
@alias issimilar is_similar
@alias issimple is_simple
@alias issimple_known is_simple_known
@alias issimultaneous_diagonalizable is_simultaneous_diagonalizable
@alias issmooth is_smooth
@alias issmooth! is_smooth!
@alias issplit is_split
@alias isstable is_stable
@alias issubfield is_subfield
@alias issubfield_normal is_subfield_normal
@alias issubgroup is_subgroup
@alias issublattice is_sublattice
@alias issublattice_with_relations is_sublattice_with_relations
@alias issurjective is_surjective
@alias istamely_ramified is_tamely_ramified
@alias istorsion is_torsion
@alias istorsion_point is_torsion_point
@alias istorsion_unit is_torsion_unit
@alias istorsion_unit_group_known is_torsion_unit_group_known
@alias istotally_complex is_totally_complex
@alias istotally_positive is_totally_positive
@alias istotally_real is_totally_real
@alias istriangular is_triangular
@alias isweakly_ramified is_weakly_ramified
@alias iszero_entry is_zero_entry
@alias iszero_mod_hnf! is_zero_mod_hnf!
@alias iszerodivisor is_zerodivisor

@alias local_genera_hermitian hermitian_local_genera
@alias local_genera_quadratic quadratic_local_genera
@alias LocalGenusHerm HermLocalGenus
@alias LocalGenusQuad QuadLocalGenus

@alias set_assert_level set_assertion_level
@alias set_verbose_level set_verbosity_level

@alias TorQuadMod TorQuadModule
@alias TorQuadModElem TorQuadModuleElem
@alias TorQuadModMor TorQuadModuleMor

@alias ZGenus ZZGenus
@alias ZLat ZZLat
@alias Zgenera integer_genera
@alias Zlattice integer_lattice
@alias ZpGenus ZZLocalGenus

# Deprecated during 0.17.*
@alias real_field real_number_field

# Deprecated during 0.19.*
@alias EmbeddedNumField EmbeddedField
@alias EmbeddedNumFieldElem EmbeddedElem
@alias EllipticCurve elliptic_curve
@alias points_with_x points_with_x_coordinate
