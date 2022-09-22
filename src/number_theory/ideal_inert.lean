import number_theory.kummer_dedekind

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]

variables {S : Type*} [comm_ring S] [algebra R S]

open ideal polynomial unique_factorization_monoid

lemma card_normalized_factors_eq_one_iff {R : Type*} [cancel_comm_monoid_with_zero R]
  [unique_factorization_monoid R] [normalization_monoid R] [decidable_eq R]
  (p : R) : (normalized_factors p).card = 1 ↔ irreducible p :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0] },
  rw multiset.card_eq_one,
  split,
  { rintro ⟨q, hq⟩,
    have hq' : q ∈ normalized_factors p,
    { simpa only [hq] using multiset.mem_singleton_self q },
    have := unique_factorization_monoid.normalized_factors_prod hp0,
    rw [hq, multiset.prod_singleton] at this,
    exact this.irreducible (irreducible_of_normalized_factor _ hq') },
  { intros hp,
    exact ⟨normalize p, unique_factorization_monoid.normalized_factors_irreducible hp⟩ },
end

open kummer_dedekind

/-- An ideal is inert if the minimal polynomial remains irreducible. -/
theorem ideal.irreducible_map_iff_irreducible_minpoly
  [is_domain S] [is_dedekind_domain S] (pb : power_basis R S)
  {I : ideal R} (hI : is_maximal I) (hI' : I.map (algebra_map R S) ≠ ⊥)
  (hpb : map I^.quotient.mk (minpoly R pb.gen) ≠ 0) :
  irreducible (I.map (algebra_map R S)) ↔
    irreducible (map I^.quotient.mk (minpoly R pb.gen)) :=
begin
  classical,
  letI : field (R ⧸ I) := ideal.quotient.field I,
  rw [← card_normalized_factors_eq_one_iff, ← card_normalized_factors_eq_one_iff,
      normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map pb hI,
      multiset.card_map, multiset.card_attach],
  unfreezingI { rintro rfl },
  simpa using hI'
end

alias ideal.irreducible_map_iff_irreducible_minpoly ↔ _ ideal.irreducible_map_of_irreducible_minpoly
