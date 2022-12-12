import number_theory.class_number_eq
import number_theory.ideal_norm

/-!
# Solving the Mordell equation

We solve the Mordell equation `y^2 = x^3 + d`, for `d ≤ -1`,
`d % 4 ∈ {2, 3}` and class number of `ℚ(√d)` not divisible by 3:

 * `mordell_d`: the Mordell equation `y^2 = x^3 + d` has solutions only if
    `d = -3m^2 ± 1` for some `m : ℕ`

## Intermediate results:
 * `gcd_lemma`: if `y^2 - d = x^3`, then `⟨y + √d⟩` and `⟨y - √d⟩` are coprime
    as ideals of `ℤ[√d]`

-/

open quad_ring
open_locale quad_ring

-- TODO list:
-- - maybe instead of using facts we can use implicit arguments?
--  e.g a lemma using dedekind_domain quad_ring can just assume that to make management of facts easier

section local_conditions
/-- There is no even x solution to `x^3 = y^2 - d`, if `d % 8 ∈ {2, 3, 5, 6, 7}`. -/
lemma x_odd_two_three_aux {x y : ℤ} {d : ℤ} (hd : ↑d ∈ ({2, 3, 5, 6, 7} : finset (zmod 8)))
  (h_eqn : y ^ 2 - d = x ^ 3) : ¬ even x :=
begin
  intro h,
  apply_fun (coe : ℤ → zmod 8) at h_eqn,
  rcases h with ⟨X, rfl⟩,
  push_cast at h_eqn,
  generalize_hyp : (y : zmod 8) = Y at h_eqn,
  generalize_hyp : (X : zmod 8) = XX at h_eqn,
  generalize_hyp : (d : zmod 8) = D at h_eqn hd,
  revert Y XX D,
  clear y d X,
  dec_trivial!
end

/-- There is no even x solution to `x^3 = y^2 - d`, if `d % 4 ∈ {2, 3}`. -/
lemma x_odd_two_three {x y : ℤ} {d : ℤ} (hd : d % 4 = 2 ∨ d % 4 = 3) (h_eqn : y ^ 2 - d = x ^ 3) :
  ¬ even x :=
begin
  refine x_odd_two_three_aux _ h_eqn,
  cases hd with hd hd;
  { rw [← euclidean_domain.div_add_mod d 4, hd],
    push_cast,
    generalize : (↑(d / 4) : zmod 8) = D,
    revert D,
    dec_trivial }
end

/-- There is no even solution to `x^3 = y^2 - d`, if `d % 4 = 3`. -/
lemma x_odd_three {x y : ℤ} {d : ℤ} (hd : d % 4 = 3) (h_eqn : y ^ 2 - d = x ^ 3) : ¬ even x :=
x_odd_two_three (or.inr hd) h_eqn

/-- There is no even solution to `x^3 = y^2 - d`, if `d % 4 = 2`. -/
lemma x_odd_two {x y : ℤ} {d : ℤ} (hd : d % 4 = 2) (h_eqn : y ^ 2 - d = x ^ 3) : ¬ even x :=
x_odd_two_three (or.inl hd) h_eqn

/-- There is no even solution to `x^3 = y^2 - d`, if `d % 8 = 5`. -/
lemma x_odd_five {x y : ℤ} {d : ℤ} (hd : d % 8 = 5) (h_eqn : y ^ 2 - d = x ^ 3) : ¬ even x :=
begin
  refine x_odd_two_three_aux _ h_eqn,
  rw [← euclidean_domain.div_add_mod d 8, hd],
  push_cast,
  generalize : (↑(d / 8) : zmod 8) = D,
  revert D,
  dec_trivial
end

end local_conditions

open ideal

lemma is_unit_of_dvd_four_mul_d_of_dvd_y_sq_sub_d {x y d : ℤ}
  [hd : fact (d % 8 = 5 ∨ d % 4 = 2 ∨ d % 4 = 3)] [hy : fact (squarefree d)]
  (h_eqn : y ^ 2 - d = x ^ 3)
  {n : ℤ} (hd4 : n ∣ d * 2 ^ 2) (hyd : n ∣ y ^ 2 - d) :
  is_unit n :=
begin
  -- Because the norm is coprime to 2, we conclude that it divides d and therefore it divides y.
  have h2 : is_coprime n 2,
  { refine (int.prime_two.coprime_iff_not_dvd.mpr _).symm,
    intros h,
    have : ¬ even (y ^ 2 - d),
    { have hodd : ¬ even x,
      { rcases hd.out with (hm|hm|hm),
        { exact x_odd_five hm h_eqn, },
        { exact x_odd_two hm h_eqn, },
        { exact x_odd_three hm h_eqn, } },
      simp only [h_eqn, hodd, not_false_iff, false_and] with parity_simps, },
    exact this (even_iff_two_dvd.mpr (h.trans hyd)) },
  have hd : n ∣ d := h2.pow_right.dvd_of_dvd_mul_right hd4,
  have hy : n ∣ y^2 := (dvd_sub_left hd).mp hyd,

  -- So it remains to show `d` and `y` are coprime.
  refine (is_coprime.pow_right _).is_unit_of_dvd' hd hy,
  -- We'll show that `(gcd d y)^2 ∣ d`, and since `d` is squarefree, conclude `gcd d y` is a unit.
  -- Here the original proof goes to `zmod (gcd |d| |y|)`. We avoid the absolute values and
  -- coercions into `zmod` by working only with divisibility.
  rw ← gcd_is_unit_iff,
  refine fact.out (squarefree d) _ _,
  -- `(gcd d y)^2 ∣ y^2`, so we can show it divides the difference, which is equal to `x^3`.
  rw [← pow_two, ← dvd_sub_right (pow_dvd_pow_of_dvd (gcd_dvd_right d y) _), h_eqn],
  -- `(gcd d y)^2 ∣ x^3` if `gcd d y` divides `x`.
  refine (pow_dvd_pow_of_dvd _ _).trans (pow_dvd_pow x (by norm_num)),
  -- Since `gcd d y` is squarefree, this is indeed the case because it divides `x^3 = y^2 - d`.
  rw [← unique_factorization_monoid.dvd_pow_iff_dvd_of_squarefree, ← h_eqn, dvd_sub_left],
  { exact (gcd_dvd_right d y).trans (dvd_pow_self _ (by norm_num)) },
  { exact gcd_dvd_left d y },
  { exact squarefree_gcd_of_squarefree_left (fact.out _) },
  { norm_num },
end

/--
The ideals (y + √d) and (y − √d) are relatively prime.
Based on the proof in Conrad, but generalised to any squarefree d ≅ 2,3 mod 4.
-/
lemma gcd_lemma {x y : ℤ} {d : ℤ} [fact $ d % 4 = 2 ∨ d % 4 = 3] [fact $ squarefree d]
  (h_eqn : y ^ 2 - d = x ^ 3) :
  gcd (ideal.span {⟨y, 1⟩} : ideal (quad_ring ℤ 0 d)) (ideal.span {⟨y, -1⟩}) = 1 :=
begin
  -- Let I and J be ⟨y + √d⟩ and ⟨y - √d⟩ respectively.
  set I := (ideal.span {⟨y, 1⟩} : ideal (quad_ring ℤ 0 d)),
  set J := (ideal.span {⟨y, -1⟩} : ideal (quad_ring ℤ 0 d)),
  -- We will show `gcd I J = I ⊔ J = 1` by showing its norm is a unit,
  -- because it divides both `d` and `y`, and those are coprime.
  rw [one_eq_top, ← ideal.abs_norm_eq_one_iff, ← int.is_unit_coe_nat],

  refine is_unit_of_dvd_four_mul_d_of_dvd_y_sq_sub_d h_eqn _ _,

  -- `(y + √d) - (y - √d) = 2 √d` is in the supremum, so the norms divide each other.
  { show (abs_norm (gcd I J) : ℤ) ∣ d * 2^2,
    have : gcd I J ∣ span ({⟨0, 2⟩} : set (quad_ring ℤ 0 d)),
    { rw [gcd_eq_sup, dvd_span_singleton],
      convert submodule.sub_mem_sup
        (submodule.mem_span_singleton_self _) (submodule.mem_span_singleton_self _) using 1,
      calc_tac },
    refine (int.coe_nat_dvd.mpr (map_dvd ideal.abs_norm this)).trans _,
    simp only [abs_norm_span_singleton, norm_eq, zero_mul, zero_add, zero_pow' 2 (by norm_num),
        zero_sub, int.nat_abs_neg, int.coe_nat_dvd_left] },
  -- Similarly `(y + √d)` is in the supremum, so the norms divide each other.
  { show ((gcd I J).abs_norm : ℤ) ∣ y^2 - d,
    refine (int.coe_nat_dvd.mpr (map_dvd ideal.abs_norm (gcd_dvd_left I J))).trans _,
    simp only [abs_norm_span_singleton, zero_mul, add_zero,
      norm_eq, one_pow, mul_one, int.coe_nat_dvd_left] },
end

lemma gcd_lemma' {x y : ℤ} {d : ℤ} (h8 : d % 8 = 5)
  [fact $ squarefree d] [fact $ ¬ is_square d] (h_eqn : y ^ 2 - d = x ^ 3) :
  by haveI : fact (d % 4 = 1) := fact.mk (by apply_fun (% 4) at h8; norm_num [int.mod_mod_of_dvd] at h8; assumption); exact
  gcd (ideal.span {⟨y - 1, 2⟩} : ideal (quad_ring ℤ 1 ((d - 1) / 4))) (ideal.span {⟨y + 1, -2⟩}) = 1 :=
begin
  haveI : fact (d % 4 = 1) := fact.mk (by apply_fun (% 4) at h8; norm_num [int.mod_mod_of_dvd] at h8; assumption),
  -- Let I and J be ⟨y - 1 + 2√d⟩ and ⟨y + 1 - 2√d⟩ respectively.
  set I := (ideal.span {⟨y - 1, 2⟩} : ideal (quad_ring ℤ 1 ((d - 1) / 4))),
  set J := (ideal.span {⟨y + 1, -2⟩} : ideal (quad_ring ℤ 1 ((d - 1) / 4))),
  -- We will show `gcd I J = I ⊔ J = 1` by showing its norm is a unit,
  -- because it divides both `d` and `y`, and those are coprime.
  rw [one_eq_top, ← abs_norm_eq_one_iff, ← int.is_unit_coe_nat],

  haveI := fact.mk h8,
  refine is_unit_of_dvd_four_mul_d_of_dvd_y_sq_sub_d h_eqn _ _,

  -- `(y - 1 + 2√d) - (y + 1 - 2√d) = -2 + 4 √d` is in the supremum, so the norms divide each other.
  { show (abs_norm (gcd I J) : ℤ) ∣ d * 2^2,
    have : gcd I J ∣ span ({⟨-2, 4⟩} : set (quad_ring ℤ 1 ((d - 1) / 4))),
    { rw [gcd_eq_sup, dvd_span_singleton],
      convert submodule.sub_mem_sup
        (submodule.mem_span_singleton_self _) (submodule.mem_span_singleton_self _) using 1,
      calc_tac },
    refine (int.coe_nat_dvd.mpr (map_dvd ideal.abs_norm this)).trans _,
    simp only [abs_norm_span_singleton, norm_eq, zero_mul, zero_add,
        zero_pow' 2 (by norm_num), zero_sub, int.nat_abs_neg, int.coe_nat_dvd_left,
        int.nat_abs, abs_norm_span_singleton, norm_eq, neg_sq, mul_neg,
        one_mul, neg_mul, int.nat_abs_dvd_iff_dvd],
    norm_num,
    rw show -4 - (d - 1) / 4 * 16 = -4 * (4 * ((d - 1) / 4) + 1), by ring,
    rw d_one_mod_four_fact,
    rw mul_comm,
    simp, },
  -- Similarly `(y - 1 + 2√d)` is in the supremum, so the norms divide each other.
  { show ((gcd I J).abs_norm : ℤ) ∣ y^2 - d,
    refine (int.coe_nat_dvd.mpr (map_dvd ideal.abs_norm (gcd_dvd_left I J))).trans _,
    simp only [abs_norm_span_singleton, norm_eq,
      int.coe_nat_dvd_left, one_mul, int.nat_abs_dvd_iff_dvd],
    ring_nf,
    rw [← neg_add', d_one_mod_four_fact, sub_eq_add_neg], },
end

open_locale non_zero_divisors

lemma factor_y_sq_sub_d (d : ℤ) (y : ℤ) :
  (y^2 - d : quad_ring ℤ 0 d) = ⟨y, 1⟩ * ⟨y, -1⟩ :=
by calc_tac

lemma factor_y_sq_sub_d_one (d : ℤ) [fact $ d % 4 = 1] (y : ℤ) :
  (y^2 - d : quad_ring ℤ 1 ((d - 1) / 4)) = ⟨y - 1, 2⟩ * ⟨y + 1, -2⟩ :=
by {calc_tac, rw [← neg_add', d_one_mod_four_fact, sub_eq_add_neg]}

/-- An integer solution to the Mordell equation `y^2 = x^3 + d`, if `¬(3 ∣ k(ℚ(√d)))`,
implies a third root of `y + √d` exists. -/
lemma exists_third_root_y_add_root (d : ℤ) (d' : ℚ) (hd : d ≤ -1)
  [fact (d % 4 = 2 ∨ d % 4 = 3)]
  [fact (squarefree d)]
  [hdd' : fact $ algebra_map ℤ ℚ d = d']
  [fact $ ¬ is_square d] [fact $ ¬ is_square d']
  (hcl : (number_field.class_number (quad_ring ℚ 0 d')).gcd 3 = 1)
  (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
  ∃ z : ℤ[√d], z^3 = ⟨y, 1⟩ :=
begin
  rw nat.gcd_comm at hcl,
  rw ← sub_eq_iff_eq_add at h_eqn,
  have : (x^3 : quad_ring ℤ 0 d) = ⟨y, 1⟩ * ⟨y, -1⟩,
  { refine trans _ (factor_y_sq_sub_d d y),
    exact_mod_cast h_eqn.symm },
  -- Since `⟨y - √d⟩` and `⟨y + √d⟩` are coprime, and `⟨y - √d⟩⟨y + √d⟩ = ⟨x⟩^3`,
  -- we have a third root `I` of `⟨y + √d⟩`.
  obtain ⟨I, hI⟩ : ∃ I : ideal (quad_ring ℤ 0 d),
    (ideal.span {⟨y, 1⟩} : ideal (quad_ring ℤ 0 d)) = I ^ 3,
  { have unit_gcd : is_unit (gcd (span ({⟨y, 1⟩} : set (quad_ring ℤ 0 d))) (span {⟨y, -1⟩})),
    { simpa using gcd_lemma h_eqn, },
    refine exists_eq_pow_of_mul_eq_pow unit_gcd (show _ = (span ({x} : set ℤ[√d]))^3, from _),
    rw [ideal.span_singleton_mul_span_singleton, ideal.span_singleton_pow, this] },
  -- The class group does not contain an element of an element of order three,
  -- and `I^3 = ⟨y + √d⟩` is principal, so `I` is principal.
  obtain ⟨z, rfl⟩ : ∃ z, I = ideal.span {z},
  { have hIn : I ∈ (ideal ℤ[√d])⁰,
    { rw mem_non_zero_divisors_iff_ne_zero,
      rintro rfl,
      rw [zero_pow, ideal.zero_eq_bot, ideal.span_singleton_eq_bot, quad_ring.ext_iff] at hI,
      { simpa using hI },
      { norm_num } },
    suffices : class_group.mk0 ⟨I, hIn⟩ = 1,
    { exact ((class_group.mk0_eq_one_iff hIn).mp this).1 },
    -- In particular, `1 = I^3 = I^(gcd k(ℚ(√d)) 3) = I^1`.
    rw [← pow_one (class_group.mk0 _), ← hcl,
        number_field.class_number_eq (quad_ring ℤ 0 d) (quad_ring ℚ 0 d'),
        ← pow_gcd_card_eq_one_iff, ← map_pow, submonoid_class.mk_pow I hIn],
    refine (class_group.mk0_eq_one_iff _).mpr _,
    rw ← hI,
    exact span.submodule.is_principal },
  -- Therefore, we have ⟨z⟩^3 = ⟨y + √d⟩, so `z^3` and `y + √d` are equal up to units.
  rw [ideal.span_singleton_pow, ideal.span_singleton_eq_span_singleton] at hI,
  rcases hI with ⟨u, hu⟩,
  -- Every unit in `ℤ[√d]` has a third root, so we find a unit v with (z * v)^3 = y + √d.
  rcases units_quad_cubes hd u with ⟨v, rfl⟩,
  use z * ↑(v⁻¹),
  rw [mul_pow, ← hu, ← units.coe_pow, inv_pow, units.mul_inv_cancel_right]
end

/-- An integer solution to the Mordell equation `y^2 = x^3 + d`, if `¬(3 ∣ k(ℚ(√d)))`,
has `y = 3dm + m^3`, where `m : ℤ` is such that `m^2 = (-d ± 1)/3`. -/
theorem Mordell_d (d : ℤ) (d' : ℚ) (hd : d ≤ -1)
  [fact (d % 4 = 2 ∨ d % 4 = 3)]
  [fact (squarefree d)]
  [hdd' : fact $ algebra_map ℤ ℚ d = d']
  [fact $ ¬ is_square d']
  (hcl : (number_field.class_number ℚ(√d')).gcd 3 = 1)
  (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
  ∃ m : ℤ, ((m : ℚ) ^ 2 = (1 - d) / 3 ∨ -(m : ℚ) ^ 2 = (1 + d) / 3) ∧ ↑y = m * (d * 3 + m ^ 2)
  :=
begin
  obtain ⟨⟨m, n⟩, h⟩ : ∃ z' : quad_ring ℤ 0 d, z' ^ 3 = (⟨y, 1⟩ : quad_ring ℤ 0 d) :=
    exists_third_root_y_add_root d d' hd hcl x y h_eqn,
  use m,
  clear' h_eqn,
  obtain ⟨hiy, hi⟩ := (quad_ring.ext_iff _ _).mp h,
  simp only [pow_succ, pow_zero, mul_b1, mul_b2, mul_one, mul_zero, add_zero] at hiy hi,
  rcases int.is_unit_eq_one_or (is_unit_of_mul_eq_one n (d * n ^ 2 + 3 * m ^ 2)
    (trans (by ring) hi)) with (rfl | rfl),
  { refine ⟨or.inl _, _⟩,
    { field_simp,
      norm_cast,
      exact eq_sub_iff_add_eq.mpr (trans (by ring) hi) },
    { norm_cast,
      exact trans hiy.symm (by ring) } },
  { simp only [one_mul, eq_self_iff_true, neg_one_sq, neg_mul, neg_add_rev, neg_neg,
      int.cast_id, eq_int_cast, nat.gcd_succ, set.mem_insert_iff, set.mem_singleton_iff] at *,
    refine ⟨or.inr _, _⟩,
    { field_simp,
      norm_cast,
      rw [eq_comm, ← eq_sub_iff_add_eq],
      exact trans hi.symm (by ring) },
    { exact trans hiy.symm (by ring) } },
end

lemma Mordell_contra {R : Type*} [comm_ring R] (d m : R)
  (hd : d = 1 - 3 * m ^ 2 ∨ d = - 1 - 3 * m ^ 2) :
  (m * (d * 3 + m ^ 2)) ^ 2 = (m ^ 2 - d) ^ 3 + d :=
by rcases hd with rfl | rfl; ring

-- local insolubility if:
-- (hd9 : ↑d ∈ ({0,2,3,4,5,6,8} : set (zmod 9)))
-- (hd3 : ↑d ∈ ({0,1} : set (zmod 3)))
theorem Mordell_minus5 (x y : ℤ) : ¬ y^2 = x^3 - 5 :=
begin
  haveI : fact ((-5 : ℤ) % 4 = 2 ∨ (-5 : ℤ) % 4 = 3) := fact.mk (or.inr (by norm_num)),
  haveI : fact (squarefree (-5 : ℤ)) := fact.mk (by norm_num [int.squarefree_iff_squarefree_nat_abs]),
  haveI : fact (algebra_map ℤ ℚ (-5 : ℤ) = -5) := fact.mk (by norm_num),
  haveI : fact (¬ is_square (-5 : ℚ)) := fact.mk (λ h, (by norm_num : ¬ (0 : ℚ) ≤ (-5)) h.nonneg), -- TODO should be easier
  intro h_eqn,
  obtain ⟨m, hm | hm, h⟩ := Mordell_d (-5) (-5) (by norm_num) (by norm_num [class_number_eq_five]) x y h_eqn,
  { norm_num at hm,
    norm_cast at hm,
    apply not_square_of_eq_two_or_three_mod_four (or.inl (show (2 % 4 : ℤ) = 2, by norm_num)),
    exact ⟨m, by simp [← hm, pow_two]⟩ },
  { cancel_denoms at hm,
    norm_cast at hm,
    apply_fun (coe : ℤ → zmod 5) at hm,
    push_cast at hm,
    revert hm,
    generalize' : (m : zmod 5) = M,
    revert M,
    dec_trivial, },
end

-- this will be an existence result
theorem Mordell_minus2 (x y : ℤ) (h_eqn : y^2 = x^3 - 2) : y = 5 ∨ y = -5 :=
begin
  haveI : fact ((-2 : ℤ) % 4 = 2 ∨ (-2 : ℤ) % 4 = 3) := fact.mk (or.inl (by norm_num)),
  haveI : fact (squarefree (-2 : ℤ)) := fact.mk (by norm_num [int.squarefree_iff_squarefree_nat_abs]),
  haveI : fact (algebra_map ℤ ℚ (-2 : ℤ) = -2) := fact.mk (by norm_num),
  haveI : fact (¬ is_square (-2 : ℚ)) := fact.mk (λ h, (by norm_num : ¬ (0 : ℚ) ≤ (-2)) h.nonneg), -- TODO should be easier
  obtain ⟨m, hm | hm, h⟩ := Mordell_d (-2) (-2) (by norm_num) (by norm_num [class_number_eq_two]) x y h_eqn,
  { norm_num at hm,
    norm_cast at hm,
    rcases hm with rfl | rfl;
    norm_num at h,
    exact or.inr h,
    exact or.inl h, },
  { cancel_denoms at hm,
    norm_cast at hm,
    apply_fun (coe : ℤ → zmod 4) at hm,
    push_cast at hm,
    revert hm,
    generalize' : (m : zmod 4) = M,
    revert M,
    dec_trivial, },
  -- { norm_num at hm, -- doesn't occur
  --   exfalso,
  --   apply_fun rat.denom at hm,
  --   norm_num at hm, -- TODO I think this entire computation should be in scope for norm_num
  --   simp at hm,
  --   rw denom_inv at hm,
  --   norm_num at hm,
  --   -- norm_num at hm,
  --   -- erw rat.denom_div_eq_of_coprime at hm,
  --   sorry, -- these goals are silly.
  --   sorry, },
end

theorem Mordell_minus6 (x y : ℤ) : ¬ y^2 = x^3 - 6 :=
begin
  haveI : fact ((-6 : ℤ) % 4 = 2 ∨ (-6 : ℤ) % 4 = 3) := fact.mk (or.inl (by norm_num)),
  haveI : fact (squarefree (-6 : ℤ)) := fact.mk (by norm_num [int.squarefree_iff_squarefree_nat_abs]),
  haveI : fact (algebra_map ℤ ℚ (-6 : ℤ) = -6) := fact.mk (by norm_num),
  haveI : fact (¬ is_square (-6 : ℚ)) := fact.mk (λ h, (by norm_num : ¬ (0 : ℚ) ≤ (-6)) h.nonneg), -- TODO should be easier
  intro h_eqn,
  obtain ⟨m, hm | hm, h⟩ := Mordell_d (-6) (-6) (by norm_num) (by norm_num [class_number_eq_six]) x y h_eqn,
  { cancel_denoms at hm,
    norm_cast at hm,
    apply_fun (coe : ℤ → zmod 8) at hm,
    push_cast at hm,
    revert hm,
    generalize' : (m : zmod 8) = M,
    revert M,
    dec_trivial, },
  { cancel_denoms at hm,
    norm_cast at hm,
    apply_fun (coe : ℤ → zmod 4) at hm,
    push_cast at hm,
    revert hm,
    generalize' : (m : zmod 4) = M,
    revert M,
    dec_trivial, }
end

theorem Mordell_minus1 (x y : ℤ) (h_eqn : y^2 = x^3 - 1) : y = 0 :=
begin
  haveI : fact ((-1 : ℤ) % 4 = 2 ∨ (-1 : ℤ) % 4 = 3) := fact.mk (or.inr (by norm_num)),
  haveI : fact (squarefree (-1 : ℤ)) := fact.mk (by norm_num [int.squarefree_iff_squarefree_nat_abs]),
  haveI : fact (algebra_map ℤ ℚ (-1 : ℤ) = -1) := fact.mk (by norm_num),
  haveI : fact (¬ is_square (-1 : ℚ)) := fact.mk (λ h, (by norm_num : ¬ (0 : ℚ) ≤ (-1)) h.nonneg), -- TODO should be easier
  obtain ⟨m, hm | hm, h⟩ := Mordell_d (-1) (-1) (by norm_num) (by norm_num [class_number_eq_one]) x y h_eqn,
  { cancel_denoms at hm,
    norm_cast at hm,
    apply_fun (coe : ℤ → zmod 4) at hm,
    push_cast at hm,
    revert hm,
    generalize' : (m : zmod 4) = M,
    revert M,
    dec_trivial, },
  { norm_num at hm,
    subst hm,
    assumption, },
end

theorem Mordell_minus13 (x y : ℤ) (h_eqn : y^2 = x^3 - 13) : y = 70 ∨ y = -70 :=
begin
  haveI : fact ((-13 : ℤ) % 4 = 2 ∨ (-13 : ℤ) % 4 = 3) := fact.mk (or.inr (by norm_num)),
  haveI : fact (squarefree (-13 : ℤ)) := fact.mk (by norm_num [int.squarefree_iff_squarefree_nat_abs]),
  haveI : fact (algebra_map ℤ ℚ (-13 : ℤ) = -13) := fact.mk (by norm_num),
  haveI : fact (¬ is_square (-13 : ℚ)) := fact.mk (λ h, (by norm_num : ¬ (0 : ℚ) ≤ (-13)) h.nonneg), -- TODO should be easier
  obtain ⟨m, hm | hm, h⟩ := Mordell_d (-13) (-13) (by norm_num) (by norm_num [class_number_eq_thirteen]) x y h_eqn,
  { cancel_denoms at hm,
    norm_cast at hm,
    apply_fun (coe : ℤ → zmod 4) at hm,
    push_cast at hm,
    revert hm,
    generalize' : (m : zmod 4) = M,
    revert M,
    dec_trivial, },
  { norm_num at hm,
    norm_cast at hm,
    have : m = -2 ∨ m = 2,
    { rw (show (4 : ℤ) = 2 ^ 2, by norm_num) at hm,
      rw sq_eq_sq_iff_eq_or_eq_neg at hm,
      exact hm.symm, },
    rcases this with rfl | rfl;
    norm_num at h; [left, right];
    assumption, },
end

#print axioms Mordell_minus1
#print axioms Mordell_minus2
#print axioms Mordell_minus5
#print axioms Mordell_minus6
#print axioms Mordell_minus13
