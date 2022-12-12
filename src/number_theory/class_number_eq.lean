import number_theory.class_number_bound
import number_theory.ideal_inert
import number_theory.legendre_symbol.norm_num

namespace quad_ring

open_locale quad_ring

local attribute [instance] fact_not_square'_of_eq_two_or_three_mod_four

open number_field

section one_calc

lemma neg_one_mod_four : fact $ (-1 : ℤ) % 4 = 3 := ⟨by norm_num⟩
lemma squarefree_neg_one : fact $ squarefree (-1 : ℤ) :=
⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩

local attribute [instance] neg_one_mod_four squarefree_neg_one

lemma sqrt_2_neg_one : (sqrt_2 (-1) : ideal (quad_ring ℤ 0 (-1))) = ideal.span {⟨1, 1⟩} :=
begin
  rw [sqrt_2, if_neg, subtype.coe_mk, set.pair_comm, ideal.span_insert_eq_span],
  { refine ideal.mem_span_singleton'.mpr ⟨⟨1, -1⟩, _⟩,
    calc_tac },
  norm_num
end

lemma card_class_group_one : fintype.card (class_group ℤ[√-1]) = 1 :=
begin
  rw [← finset.card_univ, univ_eq, finset.card_insert_of_mem, finset.card_singleton],
  { rw [finset.mem_singleton, eq_comm, class_group.sqrt_2, sqrt_2],
    exact (class_group.mk0_eq_one_iff _).mpr ⟨⟨_, sqrt_2_neg_one⟩⟩ },
  { norm_num },
  { norm_num }
end

lemma class_number_eq_one : class_number (quad_ring ℚ 0 (-1)) = 1 :=
by rw [class_number_eq (quad_ring ℤ 0 (-1)) (quad_ring ℚ 0 (-1)), card_class_group_one]

end one_calc

section two_calc

lemma neg_two_mod_four : fact $ (-2 : ℤ) % 4 = 2 := ⟨by norm_num⟩
lemma squarefree_neg_two : fact $ squarefree (-2 : ℤ) :=
⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩

local attribute [instance] neg_two_mod_four squarefree_neg_two

lemma sqrt_2_neg_two : (sqrt_2 (-2) : ideal (quad_ring ℤ 0 (-2))) = ideal.span {⟨0, 1⟩} :=
begin
  rw [sqrt_2, if_pos, subtype.coe_mk, set.pair_comm, ideal.span_insert_eq_span],
  { refine ideal.mem_span_singleton'.mpr ⟨⟨0, -1⟩, _⟩,
    calc_tac },
  norm_num
end

lemma card_class_group_two : fintype.card (class_group ℤ[√-2]) = 1 :=
begin
  rw [← finset.card_univ, univ_eq, finset.card_insert_of_mem, finset.card_singleton],
  { rw [finset.mem_singleton, eq_comm, class_group.sqrt_2, sqrt_2],
    exact (class_group.mk0_eq_one_iff _).mpr ⟨⟨_, sqrt_2_neg_two⟩⟩ },
  { norm_num },
  { norm_num }
end

lemma class_number_eq_two : class_number (quad_ring ℚ 0 (-2)) = 1 :=
by rw [class_number_eq (quad_ring ℤ 0 (-2)) (quad_ring ℚ 0 (-2)), card_class_group_two]

end two_calc

section six_calc

lemma neg_six_mod_four : fact $ (-6 : ℤ) % 4 = 2 := ⟨by norm_num⟩
lemma squarefree_neg_six : fact $ squarefree (-6 : ℤ) :=
⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩
local attribute [instance] neg_six_mod_four squarefree_neg_six

local attribute [instance] fact_not_square'_of_eq_three_mod_four
lemma card_class_group_six : fintype.card (class_group ℤ[√-6]) = 2 :=
begin
  rw [← finset.card_univ, univ_eq, finset.card_insert_of_not_mem, finset.card_singleton],
  { rw finset.mem_singleton,
    apply_fun order_of,
    rw [order_of_sqrt2, order_of_one],
    repeat { norm_num } },
  { norm_num },
  { norm_num }
end

lemma class_number_eq_six : class_number (quad_ring ℚ 0 (-6)) = 2 :=
by rw [class_number_eq (quad_ring ℤ 0 (-6)) (quad_ring ℚ 0 (-6)), card_class_group_six]

end six_calc

section five_calc

lemma neg_five_mod_four : fact $ (-5 : ℤ) % 4 = 3 := ⟨by norm_num⟩
lemma squarefree_neg_five : fact $ squarefree (-5 : ℤ) :=
⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩
local attribute [instance] neg_five_mod_four squarefree_neg_five

local attribute [instance] fact_not_square'_of_eq_three_mod_four
lemma card_class_group_five : fintype.card (class_group ℤ[√-5]) = 2 :=
begin
  rw [← finset.card_univ, univ_eq, finset.card_insert_of_not_mem, finset.card_singleton],
  { rw finset.mem_singleton,
    apply_fun order_of,
    rw [order_of_sqrt2, order_of_one],
    repeat { norm_num } },
  { norm_num },
  { norm_num }
end

lemma class_number_eq_five : class_number (quad_ring ℚ 0 (-5)) = 2 :=
by rw [class_number_eq (quad_ring ℤ 0 (-5)) (quad_ring ℚ 0 (-5)), card_class_group_five]

end five_calc

section thirteen_calc

lemma neg_thirteen_mod_four : fact $ (-13 : ℤ) % 4 = 3 := ⟨by norm_num⟩
lemma squarefree_neg_thirteen : fact $ squarefree (-13 : ℤ) :=
⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩
local attribute [instance] neg_thirteen_mod_four squarefree_neg_thirteen
-- local attribute [instance] fact_not_square'_of_eq_three_mod_four
local attribute [-instance] algebra''
-- set_option pp.implicit true

-- complete hack to avoid diamonds

def algebra''' (R S : Type*) [comm_ring R] [field S] [algebra R S] (a b : R)
  (a' b' : S) [fact (algebra_map R S a = a')] [fact (algebra_map R S b = b')] :
  algebra (quad_ring R a b) (quad_ring S a' b') :=
((quad_ring.congr (ring_equiv.refl S)
    (show _, from fact.out (algebra_map R S a = a'))
    (show _, from fact.out (algebra_map R S b = b'))).to_ring_hom.comp
  (map (algebra_map R S) a b)).to_algebra

local attribute [instance] algebra'''

open_locale non_zero_divisors

-- theorem zsqrtneg13.exists_q_r (γ : quad_ring ℚ 0 (-13)) :
--   ∃ (q : quad_ring ℤ 0 (-13)) (r ∈ ({1, 2, 3} : finset ℤ)),
--     absolute_value.abs (algebra.norm ℚ (r • γ - algebra_map ℤ[√-13] ℚ(√-13) q)) < 1 :=
-- sorry

/-- Every class in the class group contains an ideal which includes `12`. -/
lemma zsqrtneg13.exists_J
  (I : (ideal (quad_ring ℤ 0 (-13)))⁰) :
  ∃ (J : (ideal (quad_ring ℤ 0 (-13)))⁰),
    class_group.mk0 I = class_group.mk0 J ∧ ((12 : ℤ[√-13]) ∈ (J : ideal (quad_ring ℤ 0 (-13)))) :=
begin
  convert exists_mk0_eq_mk0'' absolute_value.abs I ({1, 2, 3, 4} : finset ℤ) 12 _ _ _,
  { intros m hm,
    fin_cases hm; norm_num, },
  { norm_num, },
  rw exists_lt_norm_iff_exists_le_one ℚ ℚ(√-13) absolute_value.abs (quad_ring.basis ℤ 0 (-13))
    absolute_value.abs _ _,
  { exact quad_ring.exists_q_r_thirteen },
  { intros x, rw [absolute_value.coe_abs, absolute_value.coe_abs, int.cast_abs, eq_int_cast] },
end

/-- Every class in the class group contains an ideal which includes `12`. -/
lemma zsqrtneg13.exists_J'
  (I : class_group (quad_ring ℤ 0 (-13))) :
  ∃ (J : (ideal (quad_ring ℤ 0 (-13)))⁰),
    I = class_group.mk0 J ∧ (12 : ℤ[√-13]) ∈ (J : ideal (quad_ring ℤ 0 (-13))) :=
begin
  obtain ⟨I, rfl⟩ := class_group.mk0_surjective I,
  exact zsqrtneg13.exists_J I,
end


lemma minpoly_int_root_eq {d : ℤ} [fact (¬ is_square d)] :
  minpoly ℤ (root ℤ 0 d) = minpoly_a_add_b_sqrt_d d 0 1 :=
begin
  rcases minpoly_int_eq (root ℤ 0 d) with ⟨x, hx⟩ | h,
  { simpa only [coe_b2, one_ne_zero, and_false, root, quad_ring.ext_iff] using hx, },
  exact h,
end

example : prime (3 : ℤ) := by norm_num [int.prime_iff_nat_abs_prime] -- TODO

@[simp] -- PRed
lemma is_unit_neg_iff_is_unit {α : Type*} [monoid α] [has_distrib_neg α] {a : α} :
  is_unit (-a) ↔ is_unit a :=
by erw [neg_eq_neg_one_mul, units.is_unit_units_mul ⟨(-1 : α), -1, by simp, by simp⟩]


section poly_lemmas -- all PRed
open_locale polynomial
open polynomial


variables {R: Type*} [ring R] (p q : polynomial R)
lemma polynomial.nat_degree_sub_eq_left_of_nat_degree_lt (h : nat_degree q < nat_degree p) :
  nat_degree (p - q) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))

lemma polynomial.nat_degree_sub_eq_right_of_nat_degree_lt (h : nat_degree p < nat_degree q) :
  nat_degree (p - q) = nat_degree q :=
nat_degree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))

lemma polynomial.card_roots_le_map_of_injective {A B : Type*} [comm_ring A] [comm_ring B] [is_domain A] [is_domain B]
  {p : A[X]} {f : A →+* B} (hf : function.injective f) :
  p.roots.card ≤ (p.map f).roots.card :=
begin
  by_cases hp0 : p = 0, { simp only [hp0, roots_zero, polynomial.map_zero, multiset.card_zero], },
  exact card_roots_le_map ((polynomial.map_ne_zero_iff hf).mpr hp0),
end
end poly_lemmas

@[simp] -- PRed
lemma nth_roots_two_eq_zero_iff {R : Type*} [comm_ring R] [is_domain R] {x : R} :
  polynomial.nth_roots 2 x = 0 ↔ ¬ is_square x :=
begin
  simp only [polynomial.nth_roots, multiset.eq_zero_iff_forall_not_mem, is_square,
    polynomial.mem_roots (polynomial.X_pow_sub_C_ne_zero (by norm_num: 0 < 2) x),
    sub_eq_zero, polynomial.is_root.def,
    polynomial.eval_sub, polynomial.eval_pow,
    polynomial.eval_X, polynomial.eval_C, not_exists],
  simp [eq_comm, pow_two],
end

lemma irred_span_singleton_of_prime_not_is_square (p d : ℤ) [fact (¬ is_square d)]
  [is_dedekind_domain (quad_ring ℤ 0 d)] [is_integral_closure (quad_ring ℤ 0 d) ℤ (quad_ring ℚ 0 d)]
  (hp : prime p) (hpd : ¬ is_square (d : zmod p.nat_abs)) :
  irreducible (ideal.span ({p} : set (quad_ring ℤ 0 d))) :=
begin
  have : (ideal.span ({p} : set ℤ)).is_maximal,
  { haveI : (ideal.span ({p} : set ℤ)).is_prime,
    { rwa [ideal.span_singleton_prime hp.ne_zero], },
    apply is_prime.to_maximal_ideal,
    simpa using hp.ne_zero, },
  letI : field (ℤ ⧸ ideal.span ({p} : set ℤ)) := @@ideal.quotient.field _ _ this,
  haveI : nontrivial (ℤ ⧸ ideal.span ({p} : set ℤ)),
  { refine ideal.quotient.nontrivial (λ h, _),
    apply hp.not_unit,
    simpa [ideal.span_singleton_eq_top, int.is_unit_iff, hp.ne_one] using h, },
  have := ideal.irreducible_map_of_irreducible_minpoly (quad_ring.power_basis ℤ 0 d) this _ _ _,
  { simpa [ideal.map_span], },
  { simp only [hp.ne_zero, ideal.map_span, eq_int_cast, set.image_singleton, ne.def,
      ideal.span_singleton_eq_bot, coe_eq_zero, not_false_iff], },
  { simp only [power_basis_gen, ne.def],
    exact polynomial.map_monic_ne_zero
      (minpoly.monic (is_integral_closure.is_integral ℤ (quad_ring ℚ 0 d) _)), },
  rw [power_basis_gen, minpoly_int_root_eq, minpoly_a_add_b_sqrt_d],
  simp only [mul_zero, eq_int_cast, int.cast_zero, zero_mul, sub_zero, zero_pow', ne.def,
    bit0_eq_zero, nat.one_ne_zero, not_false_iff, one_pow, mul_one, polynomial.map_add,
    polynomial.map_pow, polynomial.map_X, zero_sub, int.cast_neg,
    polynomial.map_neg, polynomial.map_int_cast],
  have hdge : 2 ≤ (polynomial.X ^ 2 - polynomial.C (↑d) : polynomial (ℤ ⧸ ideal.span ({p} : set ℤ))).nat_degree,
  { rw polynomial.nat_degree_sub_eq_left_of_nat_degree_lt;
    simp only [polynomial.nat_degree_pow, polynomial.nat_degree_X, mul_one,
      polynomial.C_eq_int_cast, polynomial.nat_degree_int_cast, nat.succ_pos'], },
  rw [← polynomial.C_eq_int_cast, ← sub_eq_add_neg],
  rw polynomial.irreducible_iff_roots_empty_of_degree_le_three (by compute_degree_le) hdge,
  rw ← multiset.card_eq_zero,
  apply nat.eq_zero_of_le_zero,
  haveI : fact p.nat_abs.prime := fact.mk (int.prime_iff_nat_abs_prime.mp hp),
  convert polynomial.card_roots_le_map_of_injective
    (int.quotient_span_equiv_zmod p).to_ring_hom.injective,

  simp only [polynomial.map_pow, polynomial.map_X, polynomial.map_sub,
    polynomial.map_int_cast, map_int_cast],
  symmetry,
  change multiset.card (polynomial.nth_roots 2 (d : zmod p.nat_abs)) = 0,
  rw multiset.card_eq_zero,
  simpa,
end


lemma prime.left_dvd_or_dvd_right_iff_dvd_mul {α : Type*} [cancel_comm_monoid_with_zero α] {p : α}
  (hp : prime p) {a b : α} : a ∣ p * b ↔ (p ∣ a ∧ a ∣ p * b) ∨ a ∣ b :=
begin
  split,
  intro h,
  simp only [h, and_true],
  exact hp.left_dvd_or_dvd_right_of_dvd_mul h,
  intro h,
  rcases h with h | h,
  exact h.2,
  exact dvd_mul_of_dvd_right h p,
end

-- TODO clean up this monstrosity
-- TODO see if there is better form that puts less dups in the goal
lemma factors_prime_mul --left_dvd_or_dvd_right_of_dvd_mul
  {α : Type*} [cancel_comm_monoid_with_zero α] {p : α}
  (hp : prime p) {b : α} : {a | a ∣ p * b} = (((*) p) '' {a | a ∣ b}) ∪ {a | a ∣ b} :=
begin
  ext a,
  simp only [set.mem_set_of_eq, set.mem_union, set.mem_image],
  conv_lhs {rw hp.left_dvd_or_dvd_right_iff_dvd_mul, },
  rw dvd_iff_exists_eq_mul_left,
  apply or_congr_left,
  intro h,
  rw ← exists_and_distrib_right,
  rw exists_congr,
  intro c,
  split; intro hh; cases hh with hh₁ hh₂,
  rw hh₁ at *,
  rw mul_comm at ⊢ hh₂,
  simp only [eq_self_iff_true, and_true],
  rwa mul_dvd_mul_iff_left hp.1 at hh₂,
  rw ← hh₂ at *,
  simp only [mul_comm, eq_self_iff_true, true_and],
  rwa mul_dvd_mul_iff_left hp.1,
end

lemma factors_prime --left_dvd_or_dvd_right_of_dvd_mul
  {α : Type*} [cancel_comm_monoid_with_zero α] [unique αˣ] {p : α}
  (hp : prime p) : {a | a ∣ p} = {1, p} :=
begin
  ext a,
  simp only [hp, set.mem_set_of_eq, set.mem_insert_iff, set.mem_singleton_iff],
  rw dvd_iff_exists_eq_mul_left,
  split; intro h,
  { rcases h with ⟨h_w, h⟩,
    have := hp.irreducible.is_unit_or_is_unit h,
    simp only [is_unit_iff_eq_one] at this,
    rcases this with rfl | rfl,
    simp * at *,
    simp, },
  { rcases h with rfl | rfl,
    use p, simp,
    use 1, simp, },
end

@[simp]
lemma class_group.mk0_span_singleton_eq_one {R : Type*} [comm_ring R] [is_domain R]
  [is_dedekind_domain R] {I : R} {h} :
  class_group.mk0 ⟨ideal.span ({I} : set R), h⟩ = 1 :=
(class_group.mk0_eq_one_iff h).mpr ⟨⟨I, rfl⟩⟩

local attribute [irreducible] non_zero_divisors

-- TODO: directly using the proof of two lemmas causes timeouts
lemma mem_of_mul_mem_non_zero_divisors_left {R : Type*} [comm_ring R]
  {I J : ideal R} (h : I * J ∈ (ideal R)⁰) :
  I ∈ (ideal R)⁰ :=
(mul_mem_non_zero_divisors.mp h).1

lemma mem_of_mul_mem_non_zero_divisors_right {R : Type*} [comm_ring R]
  {I J : ideal R} (h : I * J ∈ (ideal R)⁰) :
  J ∈ (ideal R)⁰ :=
(mul_mem_non_zero_divisors.mp h).2

@[simp]
lemma class_group.mk0_mul {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (I J : ideal R) (h : I * J ∈ (ideal R)⁰) :
  class_group.mk0 ⟨I * J, h⟩ = class_group.mk0 ⟨I, mem_of_mul_mem_non_zero_divisors_left h⟩
                          * class_group.mk0 ⟨J, mem_of_mul_mem_non_zero_divisors_right h⟩ :=
by rw ← map_mul; congr

open_locale classical

/-- the class group of `ℚ(√-13)` consists of at most two elements. -/
theorem thirteen_class_group_eq (I : class_group (quad_ring ℤ 0 (-13))) :
  I ∈ ({1, class_group.sqrt_2 (-13)} : finset (class_group ℤ[√-13])) :=
begin
  simp only [finset.mem_insert, finset.mem_singleton],
  obtain ⟨⟨J, hJ0⟩, rfl, hJ⟩ := zsqrtneg13.exists_J' I,
  have hJ2 : J ∣ ideal.span {12}, -- TODO extract this whole calculation as lemma
  { simpa only [set_like.coe_mk, ideal.dvd_iff_le, ideal.span_singleton_le_iff] using hJ },
  rw show (12 : ℤ[√-13]) = 3 * 2 * 2, by refl at hJ2, -- TODO norm_num fails??! maybe should ext first?
  rw [← ideal.span_singleton_mul_span_singleton, ← ideal.span_singleton_mul_span_singleton,
      ← sqrt_2_pow_two, pow_two, mul_assoc, mul_assoc] at hJ2,
  simp_rw ← set.mem_set_of_eq at hJ2,
  have : J ∈ {I : ideal ℤ[√-13] |
    I ∣ ideal.span ({3} : set ℤ[√-13]) * (sqrt_2 (-13) * (sqrt_2 (-13) * (sqrt_2 (-13) * sqrt_2 (-13))))},
  { rwa set.mem_set_of_eq, },
  have irred_three := irred_span_singleton_of_prime_not_is_square 3 (-13)
    (by norm_num [int.prime_iff_nat_abs_prime]) _,
  { simp only [int.cast_bit1, coe_one] at irred_three,
    -- TODO simplify this with a prime pow version
    simp only [factors_prime_mul (gcd_monoid.prime_of_irreducible irred_three),
      factors_prime_mul (sqrt_2_prime (-13)),
      factors_prime (gcd_monoid.prime_of_irreducible irred_three),
      factors_prime (sqrt_2_prime (-13))] at this,
    simp only [ideal.one_eq_top, set.image_insert, ideal.mul_top, set.image_singleton,
      set.union_insert, set.union_singleton, set.insert_eq_of_mem, set.mem_insert_iff,
      eq_self_iff_true, true_or, set.mem_singleton_iff, or_true] at this,
    have helper : sqrt_2 (-13) * sqrt_2 (-13) = ⟨ideal.span ({2} : set ℤ[√-13]),
      by norm_num [mem_non_zero_divisors_iff_ne_zero]⟩,
    { rw ← pow_two, ext1, push_cast, rw sqrt_2_pow_two (-13), },
    have helper' := subtype.ext_iff.mp helper,
    simp only [submonoid.coe_mul, set_like.coe_mk] at helper',
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl;
    simp only [
      eq_self_iff_true, true_or, or_true, -quotient_group.eq_one_iff,
      class_group.sqrt_2, helper, helper', map_bit0, map_one, mul_one, one_mul,
      set_like.eta, eq_self_iff_true, or_true, ← mul_assoc,
      class_group.mk0_span_singleton_eq_one, class_group.mk0_top] {fail_if_unchanged := ff};
    simp only [set_like.eta, class_group.mk0_mul, mul_one, one_mul, eq_self_iff_true,
      class_group.mk0_span_singleton_eq_one, or_true, true_or] {fail_if_unchanged := ff}, },
  { haveI : fact (nat.prime (int.nat_abs 3)) := ⟨by norm_num⟩,
    rw ← legendre_sym.eq_neg_one_iff,
    norm_num, }
end

-- noncomputable instance thirteen_fintype : fintype (class_group (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13))) :=
-- class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible

lemma thirteen_univ_eq : finset.univ =
  ({1, class_group.sqrt_2 (-13)} : finset (class_group (quad_ring ℤ 0 (-13)))) :=
symm $ eq_top_iff.mpr $ λ I _, thirteen_class_group_eq I


lemma card_class_group_thirteen : fintype.card (class_group ℤ[√-13]) = 2 :=
begin
  rw [← finset.card_univ, thirteen_univ_eq, finset.card_insert_of_not_mem, finset.card_singleton],
  { rw finset.mem_singleton,
    apply_fun order_of,
    rw [order_of_sqrt2, order_of_one],
    repeat { norm_num } },
end

lemma class_number_eq_thirteen : class_number (quad_ring ℚ 0 (-13)) = 2 :=
by rw [class_number_eq (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13)), card_class_group_thirteen]

end thirteen_calc

end quad_ring
