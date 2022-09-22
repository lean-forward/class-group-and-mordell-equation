import number_theory.quad_ring.basic
import number_theory.class_number_computing
import number_theory.ideal_inert
import number_theory.class_number.admissible_abs
import number_theory.class_number.finite
import number_theory.number_field
import ring_theory.localization.module
import ring_theory.ideal.norm
import tactic.compute_degree
import data.zmod.quotient
-- import number_theory.ideal_norm
import tactic.slim_check
.

namespace tactic.interactive
setup_tactic_parser
open tactic tactic.interactive
/-- `my_try_for n { tac }` executes `tac` for `n` ticks, otherwise fails -/
meta def my_try_for (max : parse parser.pexpr) (tac : itactic) : tactic unit :=
do max ← i_to_expr_strict max >>= tactic.eval_expr nat,
  λ s, match _root_.try_for max (tac s) with
  | some r := r
  | none   := result.exception none none s
  end
end tactic.interactive

open class_group ring real
open quad_ring

variables {R S ι : Type*} [euclidean_domain R] [comm_ring S] [algebra R S]
variables (K L : Type*) (abv : absolute_value R ℤ) (bS : basis ι R S)
  [is_domain S] [field K] [field L] [algebra R K] [is_fraction_ring R K] [algebra K L]
  [finite_dimensional K L] [algRL : algebra R L] [is_scalar_tower R K L]
  [algebra S L]

open_locale big_operators
open_locale non_zero_divisors
open_locale quad_ring

section to_mathlib

@[simp]
lemma ideal.span_singleton_le_iff {R : Type*} [semiring R] {x : R} {I : ideal R} :
  ideal.span {x} ≤ I ↔ x ∈ I :=
submodule.span_singleton_le_iff_mem x I

lemma ideal.span_insert_eq_span {R : Type*} [semiring R] {x : R} {s : set R}
  (h : x ∈ ideal.span s) :
  ideal.span (insert x s) = ideal.span s :=
submodule.span_insert_eq_span h

@[simp] lemma absolute_value.coe_abs {S : Type*} [linear_ordered_ring S] :
  (absolute_value.abs : S → S) = abs := rfl

lemma submodule.unique_quotient_iff_eq_top {R M : Type*} [comm_ring R]
  [add_comm_group M] [module R M] {P : submodule R M} :
  nonempty (unique (M ⧸ P)) ↔ P = ⊤ :=
begin
  split,
  { rintro ⟨h⟩,
    refine eq_top_iff.mpr (λ x _, _),
    have this : x - 0 ∈ P := (submodule.quotient.eq P).mp (by exactI subsingleton.elim _ _),
    rwa [sub_zero] at this },
  { rintro rfl,
    refine ⟨⟨⟨0⟩, _⟩⟩,
    simp }
end

lemma eq_top_iff_card_norm_eq_one {R M : Type*} [comm_ring R] [add_comm_group M]
  [module R M] {I : submodule R M} :
  I.card_norm = 1 ↔ I = ⊤ :=
begin
  rw submodule.card_norm,
  split_ifs with h,
  { rw [fintype.card_eq_one_iff_nonempty_unique, submodule.unique_quotient_iff_eq_top] },
  simp only [zero_ne_one, false_iff],
  contrapose! h,
  rw h,
  refine nonempty.intro _,
  apply_instance,
end

/-- The coordinates of `f x` in a basis `f ∘ b` are given by the coordinates of `x` in basis `b`.

This is mostly an auxiliary lemma for `basis.mk_comp_repr_self`.

In case `hf : function.injective f`, we can choose
`hli := ((f.linear_independent_iff hf).mpr b.linear_independent)`.
-/
lemma basis.mk_comp_repr_comp_self {ι R M N : Type*}
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (b : basis ι R M)
  (f : M →ₗ[R] N) (hli : linear_independent R (f ∘ b)) (hsp : submodule.span R (set.range (f ∘ b)) = ⊤) :
  ((basis.mk hli hsp.ge).repr :
    N →ₗ[R] (ι →₀ R)) ∘ₗ f = b.repr :=
begin
  refine b.ext (λ i, _),
  rw [linear_map.comp_apply, linear_equiv.coe_coe, linear_equiv.coe_coe, basis.repr_self],
  convert basis.repr_self _ i,
  rw basis.mk_apply,
end

/-- The coordinates of `f x` in a basis `f ∘ b` are given by the coordinates of `x` in basis `b`.

In case `hf : function.injective f`, we can choose
`hli := ((f.linear_independent_iff hf).mpr b.linear_independent)`.
-/
@[simp] lemma basis.mk_comp_repr_self {ι R M N : Type*}
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (b : basis ι R M) (f : M →ₗ[R] N)
  (hli : linear_independent R (f ∘ b)) (hsp : submodule.span R (set.range (f ∘ b)) = ⊤) (x : M) :
  (basis.mk hli hsp.ge).repr (f x) = b.repr x :=
by rw [← b.repr.coe_coe, ← b.mk_comp_repr_comp_self f hli hsp, linear_map.comp_apply,
       linear_equiv.coe_coe]

/- Promote a basis for `S` over `R` to a basis for `Frac(S)` over `Frac(R)`.

From the hypotheses the existence of such a basis already follows,
this is just a strengthening where the bases coincide (up to coercion).
-/
noncomputable def basis.fraction_ring {R S ι K L : Type*}
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [field K] [field L]
  [algebra R K] [algebra S L] [algebra R S] [algebra K L] [algebra R L]
  [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  -- TODO: can we weaken the hypotheses in the following lines?
  [is_integral_closure S R L] (hKL : algebra.is_algebraic K L) (b : basis ι R S) :
  basis ι K L :=
basis.mk
  (show linear_independent K (λ i, algebra_map S L (b i)),
    from ((((algebra.linear_map S L).restrict_scalars R).linear_independent_iff
        (by simpa only [linear_map.ker_eq_bot, linear_map.coe_restrict_scalars,
            algebra.coe_linear_map]
          using is_fraction_ring.injective S L)).mpr
      b.linear_independent).localization _ (R⁰))
  (begin
    have injRL : function.injective (algebra_map R L),
    { rw is_scalar_tower.algebra_map_eq R K L,
      exact (ring_hom.injective _).comp (is_fraction_ring.injective _ _) },
    have injRS : function.injective (algebra_map R S),
    { refine function.injective.of_comp (show function.injective (algebra_map S L ∘ _), from _),
      rwa [is_scalar_tower.algebra_map_eq R S L, ring_hom.coe_comp] at injRL },
    convert le_refl _,
    rw [eq_top_iff, set_like.le_def],
    rintros x -,
    obtain ⟨x, y, rfl⟩ := is_localization.mk'_surjective S⁰ x,
    -- Write `x / y : L` as `x' / y'` with `y' ∈ R⁰`.
    have : algebra.is_algebraic R L := is_fraction_ring.comap_is_algebraic_iff.mpr hKL,
    obtain ⟨x', y', hy', h⟩ :=
      is_integral_closure.exists_smul_eq_mul this injRL x (non_zero_divisors.ne_zero y.prop),
    refine (is_localization.mem_span_iff R⁰).mpr ⟨algebra_map S _ x', _, ⟨⟨y', _⟩, _⟩⟩,
    { rw [set.range_comp, ← algebra.coe_linear_map, ← linear_map.coe_restrict_scalars R,
        submodule.span_image],
      exact submodule.mem_map_of_mem (b.mem_span _),
      repeat { apply_instance } },
    { exact mem_non_zero_divisors_of_ne_zero hy' },
    { rw [algebra.smul_def, is_fraction_ring.mk'_eq_div, is_fraction_ring.mk'_eq_div],
      simp only [subtype.coe_mk, map_one, one_div, map_mul, map_inv₀ (algebra_map K L),
         ← is_scalar_tower.algebra_map_apply R K L],
      have hy0 := is_localization.to_map_ne_zero_of_mem_non_zero_divisors L le_rfl y.prop,
      have hy'0 := is_localization.to_map_ne_zero_of_mem_non_zero_divisors L le_rfl
        (map_mem_non_zero_divisors _ injRS (mem_non_zero_divisors_of_ne_zero hy')),
      rw [div_eq_iff hy0, mul_assoc, is_scalar_tower.algebra_map_apply R S L,
          eq_inv_mul_iff_mul_eq₀ hy'0, ← map_mul, ← algebra.smul_def, h, mul_comm, map_mul] },
  end)

@[simp]
lemma basis.fraction_ring_apply {R S ι K L : Type*}
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [field K] [field L]
  [algebra R K] [algebra S L] [algebra R S] [algebra K L] [algebra R L]
  [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  -- TODO: can we weaken the hypotheses in the following lines?
  [is_integral_closure S R L] (hKL : algebra.is_algebraic K L)
  (b : basis ι R S) (i : ι) :
  b.fraction_ring hKL i = algebra_map _ _ (b i) :=
by rw [basis.fraction_ring, basis.coe_mk]

@[simp]
lemma basis.fraction_ring_repr_comp_algebra_map {R S ι K L : Type*}
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [field K] [field L]
  [algebra R K] [algebra S L] [algebra R S] [algebra K L] [algebra R L]
  [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  -- TODO: can we weaken the hypotheses in the following lines?
  [is_integral_closure S R L] (hKL : algebra.is_algebraic K L)
  (b : basis ι R S) :
  ((b.fraction_ring hKL).repr.restrict_scalars R : L →ₗ[R] (ι →₀ K)) ∘ₗ
      ((algebra.linear_map S L).restrict_scalars R) =
    (finsupp.map_range.linear_map (algebra.linear_map R K)) ∘ₗ (b.repr : S →ₗ[R] (ι →₀ R)) :=
begin
  refine b.ext (λ i, _),
  rw [linear_map.comp_apply, linear_map.restrict_scalars_apply, algebra.linear_map_apply,
      linear_equiv.coe_coe, linear_equiv.restrict_scalars_apply, linear_map.comp_apply,
      linear_equiv.coe_coe, basis.repr_self, finsupp.map_range.linear_map_apply,
      finsupp.map_range_single, algebra.linear_map_apply, map_one,
      ← b.fraction_ring_apply hKL, basis.repr_self],
end

@[simp]
lemma basis.fraction_ring_repr_algebra_map {R S ι K L : Type*}
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [field K] [field L]
  [algebra R K] [algebra S L] [algebra R S] [algebra K L] [algebra R L]
  [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  -- TODO: can we weaken the hypotheses in the following lines?
  [is_integral_closure S R L] (hKL : algebra.is_algebraic K L)
  (b : basis ι R S) (x : S) (i : ι) :
  (b.fraction_ring hKL).repr (algebra_map S L x) i = algebra_map R K (b.repr x i) :=
calc (b.fraction_ring hKL).repr (algebra_map S L x) i
  = (((b.fraction_ring hKL).repr.restrict_scalars R : L →ₗ[R] (ι →₀ K)) ∘ₗ
      ((algebra.linear_map S L).restrict_scalars R)) x i : rfl
... = ((finsupp.map_range.linear_map (algebra.linear_map R K)) ∘ₗ (b.repr : S →ₗ[R] (ι →₀ R))) x i
  : by rw basis.fraction_ring_repr_comp_algebra_map
... = algebra_map R K (b.repr x i) : rfl

lemma is_fraction_ring.map_left_mul_matrix (R K S L : Type*)
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [field K] [field L]
  [algebra R K] [algebra S L] [algebra R S] [algebra K L] [algebra R L]
  [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  -- TODO: can we weaken the hypotheses in the following lines?
  [is_integral_closure S R L] (hKL : algebra.is_algebraic K L)
  [fintype ι] [decidable_eq ι] (b : basis ι R S) (x : S) :
  (algebra_map R K).map_matrix (algebra.left_mul_matrix b x) =
    algebra.left_mul_matrix (b.fraction_ring hKL) (algebra_map S L x) :=
begin
  ext i j,
  rw [ring_hom.map_matrix_apply, matrix.map_apply, algebra.left_mul_matrix_eq_repr_mul,
    algebra.left_mul_matrix_eq_repr_mul, basis.fraction_ring_apply, ← map_mul,
    basis.fraction_ring_repr_algebra_map],
end

lemma norm_fraction_ring (R K S L : Type*)
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [field K] [field L]
  [algebra R K] [algebra S L] [algebra R S] [algebra K L] [algebra R L]
  [is_scalar_tower R K L] [is_scalar_tower R S L]
  [is_fraction_ring R K] [is_fraction_ring S L]
  -- TODO: can we weaken the hypotheses in the following lines?
  [finite ι] [is_integral_closure S R L] (hKL : algebra.is_algebraic K L)
  (b : basis ι R S) (x : S) :
  algebra.norm K (algebra_map S L x) = algebra_map R K (algebra.norm R x) :=
begin
  classical,
  casesI nonempty_fintype ι,
  rw [algebra.norm_eq_matrix_det b, ring_hom.map_det,
      is_fraction_ring.map_left_mul_matrix R K S L hKL, ← algebra.norm_eq_matrix_det]
end

/-- Let `M` be a finite set of nonzero elements of `S`, so that we can approximate `a / b : L`
with `q / r`, where `r` has finitely many options for `L`.
Then each class in the class group contains an ideal `J` such that `Π m ∈ M` is in `J`.

This is a generalization of `class_group.exists_mk0_eq_mk0`, replacing `finset_approx`
with an arbitrary set `M` that satisfies the conditions.
-/
theorem exists_mk0_eq_mk0'' [is_dedekind_domain S] [is_fraction_ring S L]
  (I : (ideal S)⁰) (M : finset R) (prodM : R) (hprodM : ∀ m ∈ M, m ∣ prodM)
  (hprodMnz : algebra_map R S prodM ≠ 0) (hM : ∀ m ∈ M, algebra_map R S m ≠ 0)
  (hex : ∀ (a : S) {b : S}, b ≠ 0 → (∃ (q : S) (r : R) (H : r ∈ M),
    abv (algebra.norm R (r • a - q * b)) < abv (algebra.norm R b))) :
  ∃ (J : (ideal S)⁰), class_group.mk0 L I = class_group.mk0 L J ∧
    algebra_map _ _ prodM ∈ (J : ideal S) :=
begin
  classical,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ prodM} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { rw mem_non_zero_divisors_iff_ne_zero,
      rintro rfl,
      rw [ideal.zero_eq_bot, ideal.mul_bot] at hJ,
      exact hprodMnz (ideal.span_singleton_eq_bot.mp (I.2 _ hJ)) },
    { rw class_group.mk0_eq_mk0_iff,
      exact ⟨algebra_map _ _ prodM, b, hprodMnz, b_ne_zero, hJ⟩ },
    rw [← set_like.mem_coe, ← set.singleton_subset_iff, ← ideal.span_le, ← ideal.dvd_iff_le],
    refine (mul_dvd_mul_iff_left _).mp _,
    swap, { exact mt ideal.span_singleton_eq_bot.mp b_ne_zero },
    rw [subtype.coe_mk, ideal.dvd_iff_le, ← hJ, mul_comm],
    apply ideal.mul_mono le_rfl,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := hex a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  simp only [algebra.smul_def] at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact hprodM _ r_mem,
end

theorem exists_mk0_eq_mk0' [is_dedekind_domain S] [is_fraction_ring S L]
  (I : (ideal S)⁰) (M : finset R) (hM : ∀ m ∈ M, algebra_map R S m ≠ 0)
  (hex : ∀ (a : S) {b : S}, b ≠ 0 → (∃ (q : S) (r : R) (H : r ∈ M),
    abv (algebra.norm R (r • a - q * b)) < abv (algebra.norm R b))) :
  ∃ (J : (ideal S)⁰), class_group.mk0 L I = class_group.mk0 L J ∧
    algebra_map _ _ (∏ m in M, m) ∈ (J : ideal S) :=
begin
  have hMn : algebra_map R S (∏ m in M, m) ≠ 0,
  { simpa only [ne.def, ring_hom.map_prod, finset.prod_eq_zero_iff, not_exists], },
  exact exists_mk0_eq_mk0'' L abv I M (∏ m in M, m) (λ m, finset.dvd_prod_of_mem _) hMn hM hex,
end

end to_mathlib

include bS

/-- Translate norms in the ring of integers to norms in the field of fractions. -/
lemma exists_lt_norm_iff_exists_le_one
  (abv' : absolute_value K ℚ) [finite ι]
  (habv' : ∀ x, abv' (algebra_map R K x) = abv x) [algebra R L] [is_scalar_tower R S L]
  [is_scalar_tower R K L] [is_integral_closure S R L]
  [is_fraction_ring S L] (M : finset R) :
  (∀ (a : S) {b : S}, b ≠ 0 → ∃ (q : S) (r : R) (H : r ∈ M),
    abv (algebra.norm R (r • a - q * b)) < abv (algebra.norm R b)) ↔
  (∀ (γ : L), ∃ (q : S) (r : R) (H : r ∈ M),
    abv' (algebra.norm K (r • γ - algebra_map S L q)) < 1) :=
begin
  haveI : no_zero_smul_divisors R L := no_zero_smul_divisors.trans R K L,
  have hnorm := norm_fraction_ring R K S L (algebra.is_algebraic_of_finite K L) bS,
  have norm_eq_zero : ∀ {x : S}, algebra.norm R x = 0 → x = 0,
  { intros x hx,
    apply_fun algebra_map R K at hx,
    rw [← hnorm, map_zero, algebra.norm_eq_zero_iff] at hx,
    exact ((injective_iff_map_eq_zero (algebra_map S L)).mp (is_fraction_ring.injective S L) x) hx },
  have norm_ne_zero : ∀ {x : S}, x ≠ 0 → algebra.norm R x ≠ 0 := λ x, mt norm_eq_zero,
  split,
  { intros h γ,
    obtain ⟨n : S, d : S, hd, rfl⟩ := @is_fraction_ring.div_surjective S _ _ _ _ _ _ γ,
    rw mem_non_zero_divisors_iff_ne_zero at hd,
    have hd' : algebra_map S L d ≠ 0 := mt
      ((injective_iff_map_eq_zero (algebra_map S L)).mp (is_fraction_ring.injective S L) d) hd,
    rcases h n hd with ⟨q, r, H, hlt⟩,
    rw [← @int.cast_lt ℚ] at hlt,
    refine ⟨q, r, H,
      (mul_lt_mul_right (abv'.pos (show algebra_map R K (algebra.norm R d) ≠ 0, from _))).mp _⟩,
    { rwa [ne.def, ← hnorm, algebra.norm_eq_zero_iff] },
    { rw [one_mul, ← map_mul, ← hnorm, ← map_mul, sub_mul, smul_mul_assoc, div_mul_cancel _ hd'],
      simpa only [← habv', ← hnorm, algebra.smul_def, map_sub, map_mul,
        ← is_scalar_tower.algebra_map_apply] using hlt } },
  { intros h a b hb,
    obtain ⟨q, r, H, hqr⟩ := h (algebra_map _ _ a / algebra_map _ _ b),
    have hb' : algebra_map S L b ≠ 0 := mt
      ((injective_iff_map_eq_zero (algebra_map S L)).mp (is_fraction_ring.injective S L) b) hb,
    refine ⟨q, r, H, _⟩,
    have := (mul_lt_mul_right (abv'.pos (mt algebra.norm_eq_zero_iff.mp hb'))).mpr hqr,
    rw [one_mul, ← map_mul, ← map_mul, hnorm, sub_mul, smul_mul_assoc, div_mul_cancel _ hb']
      at this,
    simpa only [← @int.cast_lt ℚ, ← habv', ← hnorm, algebra.smul_def, map_sub, map_mul,
      ← is_scalar_tower.algebra_map_apply] using this },
end

omit bS

lemma sub_round_sq {K : Type*} [linear_ordered_field K] [floor_ring K]
  (a : K) : (a - round a)^2 ≤ 1/4 :=
calc (a - round a)^2 = |a - round a|^2 : (pow_bit0_abs _ _).symm
                 ... ≤ (1/2) ^ 2 : sq_le_sq.mpr
  (by simpa only [abs_abs, abs_eq_self.mpr (show 0 ≤ (1/2 : K), by norm_num)]
    using abs_sub_round a)
                 ... = 1/4 : by norm_num

namespace quad_ring

/-- Any `γ : ℚ(√ d)` can be approximated by a whole, or half, of some `q : ℤ[√ d]`,
when `-6 ≤ d ≤ 0`. -/
theorem sqrt_neg.exists_q_r {d : ℤ} {d' : ℚ} [hdd' : fact $ algebra_map ℤ ℚ d = d']
  (d_nonpos : d ≤ 0) (hdge : -6 ≤ d) (γ : quad_ring ℚ 0 d') :
  ∃ (q : quad_ring ℤ 0 d) (r ∈ ({1, 2} : finset ℤ)),
    absolute_value.abs (algebra.norm ℚ (r • γ - algebra_map ℤ[√ d] ℚ(√ d') q)) < 1 :=
begin
  have d'_nonpos : d' ≤ 0,
  { simpa only [← hdd'.out, int.cast_nonpos, eq_int_cast] using d_nonpos },
  have hd'ge : -6 ≤ d',
  { simpa only [← hdd'.out, eq_int_cast, int.cast_bit0, int.cast_bit1, int.cast_one, int.cast_neg]
      using (@int.cast_le ℚ _ _ _ _).mpr hdge },

  let n := round γ.b1,
  let m := round γ.b2,
  -- If the imaginary component is small enough, `γ` is close to an integral element.
  by_cases hb2 : (γ.b2 - m)^2 ≤ 1/9,
  { use [⟨n,m⟩, 1, finset.mem_insert_self 1 {2}],
    have norm_nonneg : 0 ≤ (γ.b1 - ↑n) ^ 2 - d' * (γ.b2 - ↑m) ^ 2,
    { simpa only [quad_ring.norm_eq, zero_mul, add_zero] using norm_nonneg d'_nonpos (γ - ⟨n, m⟩) },
    simp only [quad_ring.norm_eq, zsmul_eq_mul, int.cast_one, one_mul, algebra_map_mk,
      sub_b1, sub_b2, absolute_value.coe_abs, abs_of_nonneg norm_nonneg, zero_mul, add_zero],
    -- Help `linarith` with the nonlinear part of the inequality
    have : (γ.b1 - ↑n) ^ 2 ≤ 1/4 := sub_round_sq γ.b1,
    have := mul_le_mul_of_nonpos_left hb2 d'_nonpos,
    linarith },
  -- Otherwise we have to choose a point halfway between integral elements.
  -- The value of `m'` is not quite as easy to put in a formula, so we'll work with its properties.
  let n' := round (2 * γ.b1),
  rsuffices ⟨m', hm'⟩ : ∃ m' : ℤ, (2 * γ.b2 - m')^2 ≤ 1/9,
  { refine ⟨⟨n', m'⟩, 2, finset.mem_insert_of_mem (finset.mem_singleton_self _), _⟩,
    have norm_nonneg : 0 ≤ (2 * γ.b1 - n') ^ 2 - d' * (2 * γ.b2 - m') ^ 2,
    { simpa only [quad_ring.norm_eq, zero_mul, add_zero, quad_ring.sub_b1, quad_ring.sub_b2, quad_ring.smul_b1,
          quad_ring.smul_b2, smul_eq_mul]
        using quad_ring.norm_nonneg d'_nonpos ((2 : ℚ) • γ - ⟨n', m'⟩) },
    simp only [zsmul_eq_mul, int.cast_bit0, int.cast_one, algebra_map_mk, norm_eq,
      sub_b1, mul_b1, bit0_b1, one_b1, bit0_b2, one_b2, bit0_zero, zero_mul,
      add_zero, sub_b2, mul_b2, zero_add, absolute_value.coe_abs, abs_of_nonneg norm_nonneg],
    -- Help `linarith` with the nonlinear part of the inequality
    have : (2 * γ.b1 - n') ^ 2 ≤ 1/4 := sub_round_sq (2 * γ.b1),
    have := mul_le_mul_of_nonpos_left hm' d'_nonpos,
    linarith },
  -- Let's modify the equations into a more linear form:
  obtain ⟨half_le, le_half⟩ : - (1/2) ≤ γ.b2 - m ∧ γ.b2 - m ≤ 1/2 := abs_le.mp (abs_sub_round γ.b2),
  have third_sq : (1/3 : ℚ)^2 = 1/9, { norm_num },
  have abs_third : |(1/3 : ℚ)| = 1/3, { norm_num },
  simp only [← third_sq, abs_third, sq_le_sq, abs_le] at ⊢,
  simp only [not_le, ← third_sq, abs_third, sq_lt_sq, lt_abs] at hb2,
  -- Depending on the difference between `γ.b2` and `m`, round up or down:
  cases hb2 with hb2_lt hb2_gt,
  { use 2 * m + 1,
    simp only [int.cast_mul, int.cast_add, int.cast_bit0, int.cast_one, ← sub_sub, ← mul_sub],
    split; linarith },
  { use 2 * m - 1,
    simp only [int.cast_mul, int.cast_sub, int.cast_bit0, int.cast_one, ← sub_add, ← mul_sub],
    split; linarith },
end


section missing
variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

open int

@[simp] lemma fract_add_nat (a : α) (m : ℕ) : fract (a + m) = fract a :=
by { rw fract, simp }

@[simp] lemma int.ceil_add_nat (a : α) (n : ℕ) : ⌈a + n⌉ = ⌈a⌉ + n :=
by rw [← int.cast_coe_nat, ceil_add_int]

end missing

section round_lemmas

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

@[simp]
lemma round_add_int (x : α) (y : ℤ) : round (x + y) = round x + y :=
by rw [round, round, int.fract_add_int, int.floor_add_int, int.ceil_add_int, ← apply_ite2, if_t_t]
-- by rw [round_eq, round_eq, ← int.floor_add_int, -- TODO weird name
--     add_right_comm x y]

@[simp]
lemma round_add_one (a : α) : round (a + 1) = round a + 1 :=
by { convert round_add_int a 1, exact int.cast_one.symm }

@[simp]
lemma round_sub_int (x : α) (y : ℤ) : round (x - y) = round x - y :=
by { rw [sub_eq_add_neg], norm_cast, rw [round_add_int, sub_eq_add_neg] }


@[simp]
lemma round_sub_one (a : α) : round (a - 1) = round a - 1 :=
by { convert round_sub_int a 1, exact int.cast_one.symm }

@[simp]
lemma round_add_nat (x : α) (y : ℕ) : round (x + y) = round x + y :=
by rw [round, round, fract_add_nat, int.floor_add_nat, int.ceil_add_nat, ← apply_ite2, if_t_t]

@[simp]
lemma round_sub_nat (x : α) (y : ℕ) : round (x - y) = round x - y :=
by { rw [sub_eq_add_neg, ← int.cast_coe_nat], norm_cast, rw [round_add_int, sub_eq_add_neg] }

@[simp]
lemma round_int_add (x : α) (y : ℤ) : round ((y : α) + x) = y + round x :=
by { rw [add_comm, round_add_int, add_comm] }

@[simp]
lemma round_nat_add (x : α) (y : ℕ) : round ((y : α) + x) = y + round x :=
by { rw [add_comm, round_add_nat, add_comm] }

end round_lemmas

section general_statement
open floor_semiring

lemma one_dim'_special {x : ℚ} (hx : int.fract x ≤ 1/2) : ∃ r : ℕ, r ≤ 4 ∧ 1 ≤ r ∧
  |↑r * x - ↑(round (↑r * x))| ≤ 6/25 :=
begin
  have h₀ : 0 ≤ int.fract x := int.fract_nonneg x,
  rw ← int.floor_add_fract x,
  simp only [mul_add],
  norm_cast,
  simp only [round_int_add, int.cast_add, add_sub_add_left_eq_sub],
  simp_rw abs_sub_round_eq_min,
  -- generalize hx : int.fract x = X,
  -- rw hx at *,
  by_cases h₁ : int.fract x < 1/5,
  { use [1, by norm_num, by norm_num],
    simp only [nat.cast_one, one_mul, int.fract_fract, min_le_iff],
    left,
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    },
  by_cases h₂ : int.fract x < 1/4,
  { use [4, by norm_num, by norm_num],
    -- simp only [not_lt] at h₁,
    simp only [nat.cast_one, nat.cast_bit0, min_le_iff, tsub_le_iff_right],
    right,
    rw int.fract_eq_self.mpr,
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    split,
    linarith,
    linarith,
    },
  by_cases h₃ : int.fract x < 3/10,
  { use [4, by norm_num, by norm_num],
    -- simp only [not_lt] at h₂,
    simp only [nat.cast_one, nat.cast_bit0, min_le_iff, tsub_le_iff_right],
    left,
    rw ((int.fract_eq_iff).mpr _ : int.fract (4 * int.fract x) = 4 * int.fract x - 1),
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    split,
    linarith,
    split,
    linarith,
    use 1,
    simp, },
  by_cases h₄ : int.fract x < 1/3,
  { use [3, by norm_num, by norm_num],
    -- simp only [not_lt] at h₂,
    simp only [nat.cast_one, nat.cast_bit1, nat.cast_bit0, min_le_iff, tsub_le_iff_right],
    right,
    rw ((int.fract_eq_iff).mpr _ : int.fract (3 * int.fract x) = 3 * int.fract x),
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    split,
    linarith,
    split,
    linarith,
    use 0,
    simp, },
  by_cases h₅ : int.fract x < 2/5,
  { use [3, by norm_num, by norm_num],
    -- simp only [not_lt] at h₂,
    simp only [nat.cast_one, nat.cast_bit1, nat.cast_bit0, min_le_iff, tsub_le_iff_right],
    left,
    rw ((int.fract_eq_iff).mpr _ : int.fract (3 * int.fract x) = 3 * int.fract x - 1),
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    split,
    linarith,
    split,
    linarith,
    use 1,
    simp, },
  by_cases h₆ : int.fract x < 1/2,
  { use [2, by norm_num, by norm_num],
    -- simp only [not_lt] at h₂,
    simp only [nat.cast_one, nat.cast_bit1, nat.cast_bit0, min_le_iff, tsub_le_iff_right],
    right,
    rw ((int.fract_eq_iff).mpr _ : int.fract (2 * int.fract x) = 2 * int.fract x),
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    split,
    linarith,
    split,
    linarith,
    use 0,
    simp, },
  { use [2, by norm_num, by norm_num],
    -- simp only [not_lt] at h₂,
    simp only [nat.cast_one, nat.cast_bit1, nat.cast_bit0, min_le_iff, tsub_le_iff_right],
    left,
    rw ((int.fract_eq_iff).mpr _ : int.fract (2 * int.fract x) = 2 * int.fract x - 1),
    linarith, -- TODO linarith breaks if 1/4 is 4⁻¹!!!!!!!
    split,
    linarith,
    split,
    linarith,
    use 1,
    simp, },
end

lemma int.fract_neg {x : ℚ} (hx : int.fract x ≠ 0) :  -- TODO generalize
  int.fract (-x) = 1 - int.fract x :=
begin
  rw int.fract_eq_iff,
  have := int.fract_lt_one x,
  split,
  linarith,
  split,
  have hhl : 0 < int.fract x := lt_of_le_of_ne' (int.fract_nonneg x) hx, -- TODO why doesn't linarith know this?
  linarith,
  use [-⌊x⌋ - 1],
  simp only [sub_sub_eq_add_sub, int.cast_sub, int.cast_neg, int.cast_one, sub_left_inj],
  conv in (-x) {rw ← int.floor_add_fract x},
  simp [-int.floor_add_fract],
end

@[simp]
lemma int.fract_neg_eq_zero {x : ℚ} :  -- TODO generalize
  int.fract (-x) = 0 ↔ int.fract x = 0 :=
begin
  rw int.fract_eq_iff,
  rw int.fract_eq_iff,
  simp only [le_refl, zero_lt_one, tsub_zero, true_and],
  split; rintros ⟨z, hz⟩; use [-z]; simp [← hz],
end

lemma one_dim' (x : ℚ) : ∃ r : ℕ, r ≤ 4 ∧ 1 ≤ r ∧
  |↑r * x - ↑(round (↑r * x))| ≤ 6/25 :=
begin
  by_cases h : int.fract x ≤ 1/2,
  { exact one_dim'_special h, },
  { simp only [not_le] at h,
    have : int.fract (-x) < 1/2,
    { rw int.fract_neg, linarith, linarith, },
    have := one_dim'_special this.le,
    apply Exists.imp _ this,
    intro r,
    simp only [mul_neg, and_imp],
    intros hr1 hr2 h,
    simp only [abs_sub_round_eq_min, hr1, hr2, min_le_iff, tsub_le_iff_right, true_and] at h ⊢,
    cases h with h h,
    { by_cases hz : int.fract (-(↑r * x)) = 0,
      { rw int.fract_neg_eq_zero at hz, simp [hz], left, norm_num, },
      have := int.fract_neg hz,
      simp only [neg_neg] at this,
      rw this,
      right,
      linarith, },
    { by_cases hz : int.fract (-(↑r * x)) = 0,
      { rw int.fract_neg_eq_zero at hz, simp [hz], left, norm_num, },
      have := int.fract_neg hz,
      simp only [neg_neg] at this,
      rw this,
      left,
      linarith, }, },
end

theorem quad_ring.exists_q_r_thirteen (γ : quad_ring ℚ 0 (-13)) :
  ∃ (q : quad_ring ℤ 0 (-13)) (r ∈ finset.Icc (1 : ℤ) 4),
    absolute_value.abs (algebra.norm ℚ (r • γ - algebra_map (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13)) q)) < 1 :=
begin
  rcases one_dim' γ.b2 with ⟨r, hl, hr, hb⟩,
  refine ⟨⟨round ((r : ℚ) * γ.b1) , round ((r : ℚ) * γ.b2)⟩, r, _, _⟩,
  { simp [one_div, finset.mem_Icc, hl, hr],
    exact_mod_cast hl, },
  { simp only [zsmul_eq_mul, algebra_map_mk, norm_eq, sub_b1, mul_b1, coe_int_b1, coe_int_b2,
      zero_mul, add_zero, sub_b2, mul_b2, zero_add],
    calc _ ≤ _ : abs_sub _ _
     ...   < 1 : _,
    simp only [abs_pow, pow_bit0_abs],
    suffices : |(-13) * (↑r * γ.b2 - ↑(round (↑r * γ.b2))) ^ 2| < 3/4,
    { norm_cast,
      push_cast, -- TODO ??????
      nlinarith [sub_round_sq (↑r * γ.b1)], },
    simp only [abs_mul, abs_pow, pow_bit0_abs],
    norm_num,
    suffices : (abs (↑r * γ.b2 - ↑(round (↑r * γ.b2))) : ℝ) < sqrt (3 / (4 * 13)),
    { rw [lt_sqrt (abs_nonneg _), div_mul_eq_div_div,
        lt_div_iff' (by linarith : 0 < (13 : ℝ)), sq_abs] at this,
      rw show (3 / 4 : ℝ) = ↑(3 / 4 : ℚ), by {cancel_denoms; norm_cast} at this, -- TODO this is awful
      exact_mod_cast this, },
    conv_lhs { norm_cast, },
    norm_cast,
    calc _ ≤ 6/25 : _
      ...  < _ : _,
    rw show (6 / 25 : ℝ) = ↑(6 / 25 : ℚ), by {cancel_denoms; norm_cast}, -- TODO this is awful
    exact_mod_cast hb,
    norm_cast,
    rw lt_sqrt (by linarith : (0 : ℝ) ≤ 6 / 25),
    norm_num, },
end

end general_statement

section

instance fact.or_left {P Q : Prop} [fact P] : fact $ P ∨ Q := fact.mk (or.inl $ fact.out _)
instance fact.or_right {P Q : Prop} [fact Q] : fact $ P ∨ Q := fact.mk (or.inr $ fact.out _)

 -- `d` is a free variable so this can't be an instance
local attribute [instance] fact_not_square'_of_eq_two_or_three_mod_four

/-- Every class in the class group contains an ideal which includes `2`. -/
lemma sqrt_neg.exists_J {d : ℤ} {d' : ℚ} [fact (algebra_map ℤ ℚ d = d')]
  [fact $ d % 4 = 2 ∨ d % 4 = 3] [fact $ squarefree d]
  (d_nonpos : d ≤ 0) (hd' : -6 ≤ d) (I : (ideal (quad_ring ℤ 0 d))⁰) :
  ∃ (J : (ideal (quad_ring ℤ 0 d))⁰),
    class_group.mk0 (quad_ring ℚ 0 d') I = class_group.mk0 (quad_ring ℚ 0 d') J ∧
    (2 : ℤ[√ d]) ∈ (J : ideal (quad_ring ℤ 0 d)) :=
begin
  refine exists_mk0_eq_mk0' ℚ(√ d') absolute_value.abs I ({1, 2} : finset ℤ) _ _,
  { rintro m (H | H | _ | _); simp only [H, eq_int_cast, quad_ring.coe_one, int.cast_bit0],
    { exact one_ne_zero },
    { exact two_ne_zero' } },
  rw exists_lt_norm_iff_exists_le_one ℚ ℚ(√ d') absolute_value.abs (quad_ring.basis ℤ 0 d)
    absolute_value.abs _ _,
  { exact sqrt_neg.exists_q_r d_nonpos hd' },
  { intros x, rw [absolute_value.coe_abs, absolute_value.coe_abs, int.cast_abs, eq_int_cast] },
end

-- TODO rename
/-- Every class in the class group contains an ideal which includes `2`. -/
lemma sqrt_neg.exists_J' {d : ℤ} {d' : ℚ} [fact (algebra_map ℤ ℚ d = d')]
  [fact $ d % 4 = 2 ∨ d % 4 = 3] [fact $ squarefree d]
  (d_nonpos : d ≤ 0) (hd' : -6 ≤ d) (I : class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d')) :
  ∃ (J : (ideal (quad_ring ℤ 0 d))⁰),
    I = class_group.mk0 (quad_ring ℚ 0 d') J ∧
    (2 : ℤ[√ d]) ∈ (J : ideal (quad_ring ℤ 0 d)) :=
begin
  obtain ⟨I, rfl⟩ := class_group.mk0_surjective I,
  exact sqrt_neg.exists_J d_nonpos hd' I,
end
end

open_locale classical

/-- `ideal.card_norm` as a monoid homomorphism -/
@[simps]
noncomputable def ideal.norm_hom (S : Type*) [comm_ring S] [is_domain S] [is_dedekind_domain S]
  [_root_.module.free ℤ S] [_root_.module.finite ℤ S] :
  ideal S →* ℕ :=
{ to_fun := submodule.card_norm,
  map_one' := by rw [ideal.one_eq_top, submodule.card_norm_top],
  -- map_mul' := card_norm_mul (module.free.choose_basis ℤ S), -- Should work but times out...
  map_mul' := λ I J, by rw [card_norm_mul (module.free.choose_basis ℤ S)] }

@[simp] lemma card_norm_span_singleton [_root_.module.free ℤ S] [_root_.module.finite ℤ S]
  {x : S} :
  (ideal.span ({x} : set S)).card_norm = (algebra.norm ℤ x).nat_abs :=
int.coe_nat_inj (by rw [← ideal.card_norm_eq_norm (module.free.choose_basis ℤ S),
  ideal.norm_span_singleton (module.free.choose_basis ℤ S), int.coe_nat_abs_eq_normalize])

@[simp] lemma card_norm_eq_of_card_norm_sq_eq_sq [_root_.module.free ℤ S] [_root_.module.finite ℤ S]
  [is_dedekind_domain S] {I : ideal S} {n : ℕ} (h : (I^2).card_norm = n^2) :
  I.card_norm = n :=
begin
  rw [pow_two, pow_two, card_norm_mul (module.free.choose_basis ℤ S), ← pow_two, ← pow_two] at h,
  exact @nat.pow_left_injective 2 (by norm_num) _ _ h
end

-- `d` is a free variable so this can't be an instance
local attribute [instance] fact_not_square'_of_eq_two_or_three_mod_four

/-- The square root of 2 is a prime element of the monoid of ideals. -/
lemma sqrt_2_prime (d : ℤ) [fact $ d % 4 = 2 ∨ d % 4 = 3] [hsq : fact $ squarefree d] :
  prime (sqrt_2 d : ideal ℤ[√ d]) :=
begin
  rw ← unique_factorization_monoid.irreducible_iff_prime,
  refine irreducible_of_map_irreducible
    (ideal.norm_hom (quad_ring ℤ 0 d))
    (λ x hx, by rwa [ideal.one_eq_top, ← eq_top_iff_card_norm_eq_one])
    _,
  have : submodule.card_norm (sqrt_2 d : ideal (quad_ring ℤ 0 d)) = 2,
  { refine card_norm_eq_of_card_norm_sq_eq_sq _, -- TODO: compute this directly
    rw [sqrt_2_pow_two _, card_norm_span_singleton],
    norm_num },
  norm_num [this, irreducible_iff_nat_prime],
end

/-- For `-6 ≤ d ≤ 0`, the class group of `ℚ(√ d)` consists of at most two elements. -/
theorem class_group_eq {d : ℤ} {d' : ℚ} [fact (algebra_map ℤ ℚ d = d')]
  [fact $ d % 4 = 2 ∨ d % 4 = 3] [hsq : fact $ squarefree d]
  (d_nonpos : d ≤ 0) (hd' : -6 ≤ d) (I : class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d')) :
  I ∈ ({1, class_group.sqrt_2 d d'} :
    finset (class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d'))) :=
begin
  simp only [finset.mem_insert, finset.mem_singleton],
  obtain ⟨⟨J, hJ0⟩, rfl, hJ⟩ := sqrt_neg.exists_J' d_nonpos hd' I,
  -- TODO: do this by showing the class group is generated by the primes dividing 2 (in this case)
  have hJ2 : J ∣ ideal.span {2},
  { simpa only [set_like.coe_mk, ideal.dvd_iff_le, ideal.span_singleton_le_iff] using hJ },
  rw [← sqrt_2_pow_two, dvd_prime_pow (sqrt_2_prime d)] at hJ2,
  obtain ⟨n, hn, J_eq⟩ := hJ2,
  rcases associated_iff_eq.mp J_eq with rfl,
  have hn' : n < 3 := by linarith,
  have := n.zero_le,
  interval_cases using this hn',
  { simp only [fractional_ideal.coe_ideal_top, set_like.coe_mk, true_or, eq_self_iff_true,
      quotient_group.coe_one, class_group.mk0_apply, units.mk0_one, ideal.one_eq_top, pow_zero] },
  { simp only [set_like.eta, class_group.sqrt_2, quotient_group.eq_one_iff, eq_self_iff_true,
      class_group.mk0_apply, pow_one, or_true, monoid_hom.mem_range] },
  { simp only [set_like.coe_mk, mk0_apply, quotient_group.eq_one_iff, monoid_hom.mem_range,
      to_principal_ideal_eq_iff, units.coe_mk0],
    refine or.inl ⟨units.mk0 2 (ne_zero.ne 2), _⟩,
    simp only [sqrt_2_pow_two, units.coe_mk0, fractional_ideal.coe_ideal_span_singleton, map_bit0,
      map_one], },
end

noncomputable instance {d : ℤ} {d' : ℚ} [fact (algebra_map ℤ ℚ d = d')]
  [fact $ d % 4 = 2 ∨ d % 4 = 3] [hsq : fact $ squarefree d] :
  fintype (class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d')) :=
class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible

lemma univ_eq {d : ℤ} {d' : ℚ} [fact (algebra_map ℤ ℚ d = d')]
  [fact $ d % 4 = 2 ∨ d % 4 = 3] [hsq : fact $ squarefree d]
  (d_nonpos : d ≤ 0) (hd' : -6 ≤ d) :
  finset.univ = ({1, class_group.sqrt_2 d d'} :
    finset (class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d'))) :=
symm $ eq_top_iff.mpr $ λ I _, class_group_eq d_nonpos hd' I

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

local attribute [instance] fact_not_square'_of_eq_three_mod_four
lemma card_class_group_one : fintype.card (class_group ℤ[√ -1] ℚ(√ -1)) = 1 :=
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

lemma card_class_group_two : fintype.card (class_group ℤ[√ -2] ℚ(√ -2)) = 1 :=
begin
  rw [← finset.card_univ, univ_eq, finset.card_insert_of_mem, finset.card_singleton],
  { rw [finset.mem_singleton, eq_comm, class_group.sqrt_2, sqrt_2],
    exact (class_group.mk0_eq_one_iff _).mpr ⟨⟨_, sqrt_2_neg_two⟩⟩ },
  { norm_num },
  { norm_num }
end

lemma class_number_eq_two : class_number (quad_ring ℚ 0 (-2)) = 1 :=
by rw [class_number_eq (quad_ring ℤ 0 (-2)) (quad_ring ℚ 0 (-2)), card_class_group_two]
open number_field

end two_calc

section six_calc

lemma neg_six_mod_four : fact $ (-6 : ℤ) % 4 = 2 := ⟨by norm_num⟩
lemma squarefree_neg_six : fact $ squarefree (-6 : ℤ) :=
⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩
local attribute [instance] neg_six_mod_four squarefree_neg_six

local attribute [instance] fact_not_square'_of_eq_three_mod_four
lemma card_class_group_six : fintype.card (class_group ℤ[√ -6] ℚ(√ -6)) = 2 :=
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
lemma card_class_group_five : fintype.card (class_group ℤ[√ -5] ℚ(√ -5)) = 2 :=
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


-- theorem zsqrtneg13.exists_q_r (γ : quad_ring ℚ 0 (-13)) :
--   ∃ (q : quad_ring ℤ 0 (-13)) (r ∈ ({1, 2, 3} : finset ℤ)),
--     absolute_value.abs (algebra.norm ℚ (r • γ - algebra_map ℤ[√ -13] ℚ(√ -13) q)) < 1 :=
-- sorry

/-- Every class in the class group contains an ideal which includes `12`. -/
lemma zsqrtneg13.exists_J
  (I : (ideal (quad_ring ℤ 0 (-13)))⁰) :
  ∃ (J : (ideal (quad_ring ℤ 0 (-13)))⁰),
    class_group.mk0 (quad_ring ℚ 0 (-13)) I = class_group.mk0 (quad_ring ℚ 0 (-13)) J ∧
    ((12 : ℤ[√ -13]) ∈ (J : ideal (quad_ring ℤ 0 (-13)))) :=
begin
  convert exists_mk0_eq_mk0'' ℚ(√ -13) absolute_value.abs I ({1, 2, 3, 4} : finset ℤ) 12 _ _ _ _,
  { intros m hm,
    fin_cases hm; norm_num, },
  { norm_num, },
  { rintro m (H | H | _ | _ | _ | _); simp only [H, eq_int_cast, quad_ring.coe_one, int.cast_bit0],
    { exact one_ne_zero },
    { exact two_ne_zero' },
    { norm_num, },
    { norm_num, }, },
  rw exists_lt_norm_iff_exists_le_one ℚ ℚ(√ -13) absolute_value.abs (quad_ring.basis ℤ 0 (-13))
    absolute_value.abs _ _,
  { exact quad_ring.exists_q_r_thirteen },
  { intros x, rw [absolute_value.coe_abs, absolute_value.coe_abs, int.cast_abs, eq_int_cast] },
end

/-- Every class in the class group contains an ideal which includes `12`. -/
lemma zsqrtneg13.exists_J'
  (I : class_group (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13))) :
  ∃ (J : (ideal (quad_ring ℤ 0 (-13)))⁰),
    I = class_group.mk0 (quad_ring ℚ 0 (-13)) J ∧
    (12 : ℤ[√ -13]) ∈ (J : ideal (quad_ring ℤ 0 (-13))) :=
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

-- example : prime (3 : ℤ) := by norm_num -- TODO

-- TODO generalize this to some congruence condition or just d not being a square mod p
lemma irred_three : irreducible (ideal.span ({3} : set (quad_ring ℤ 0 (-13)))) :=
begin
  have : (ideal.span ({3} : set ℤ)).is_maximal,
  { haveI : (ideal.span ({3} : set ℤ)).is_prime,
    { rw [ideal.span_singleton_prime, int.prime_iff_nat_abs_prime]; -- TODO why doesn't norm_num
      norm_num, },
    apply is_prime.to_maximal_ideal,
    norm_num, },
  letI : field (ℤ ⧸ ideal.span ({3} : set ℤ)) := @@ideal.quotient.field _ _ this,
  haveI : nontrivial (ℤ ⧸ ideal.span ({3} : set ℤ)),
  { refine ideal.quotient.nontrivial (λ h, _),
    norm_num [ideal.span_singleton_eq_top, int.is_unit_iff] at h, },
  have := ideal.irreducible_map_of_irreducible_minpoly (quad_ring.power_basis ℤ 0 (-13)) this _ _ _,
  { simpa [ideal.map_span], },
  { simp only [ideal.map_span, eq_int_cast, set.image_singleton, int.cast_bit1, coe_one,
      ne.def, ideal.span_singleton_eq_bot], norm_num, },
  { simp only [power_basis_gen, ne.def],
    exact polynomial.map_monic_ne_zero
      (minpoly.monic (is_integral_closure.is_integral ℤ (quad_ring ℚ 0 (-13)) _)), },
  rw [power_basis_gen, minpoly_int_root_eq, minpoly_a_add_b_sqrt_d],
  simp only [mul_zero, eq_int_cast, int.cast_zero, zero_mul, sub_zero, zero_pow', ne.def,
    bit0_eq_zero, nat.one_ne_zero, not_false_iff, one_pow, neg_mul, mul_one, sub_neg_eq_add,
    zero_add, polynomial.C_bit1, polynomial.C_bit0, int.cast_one, polynomial.map_add,
    polynomial.map_pow, polynomial.map_X, polynomial.map_bit1, polynomial.map_bit0,
    polynomial.map_one],
  have hdge : 2 ≤ (polynomial.X ^ 2 + 13 : polynomial (ℤ ⧸ ideal.span ({3} : set ℤ))).nat_degree,
  { rw polynomial.nat_degree_add_eq_left_of_nat_degree_lt;
    simp only [polynomial.nat_degree_pow, polynomial.nat_degree_X,
      mul_one, nat.one_le_bit0_iff, nat.lt_one_iff],
    apply (polynomial.nat_degree_bit1 _).trans_lt, -- ah yes 13 in binary
    apply (polynomial.nat_degree_bit0 _).trans_lt,
    apply (polynomial.nat_degree_bit1 _).trans_lt,
    simp only [nat.succ_pos', polynomial.nat_degree_one], },
  rw polynomial.irreducible_iff_roots_empty_of_degree_le_three (by compute_degree_le) hdge,
  { rw multiset.eq_zero_iff_forall_not_mem,
    rw (int.quotient_span_equiv_zmod 3).to_equiv.forall_congr_left',
    rintro ⟨y, hy : y < 3⟩,
    simp,
    have hp : (polynomial.X ^ 2 + 13 : polynomial (ℤ ⧸ ideal.span ({3} : set ℤ))) ≠ 0,
    { intro h,
      norm_num [h] at hdge, },
    interval_cases y;
    rw [polynomial.mem_roots hp, polynomial.is_root.def],
    -- all cases here are basically the same, but we need to "pick" a preimage under
    -- ideal.quotient.mk so its hard to make this nicer without a little meta
    { simp only [fin.mk_zero, map_zero, polynomial.eval_add, polynomial.eval_pow, polynomial.eval_X,
        zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero, not_false_iff, polynomial.eval_bit1,
        polynomial.eval_bit0, polynomial.eval_one, zero_add],
      rw (show (13 : (ℤ ⧸ ideal.span ({3} : set ℤ))) = ideal.quotient.mk _ 13, by simp),
      rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton],
      norm_num, },
    { norm_num,
      rw (show (14 : (ℤ ⧸ ideal.span ({3} : set ℤ))) = ideal.quotient.mk _ 14, by simp),
      rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton],
      norm_num, },
    { simp only [fin.mk_bit0, map_bit0, polynomial.eval_add, polynomial.eval_pow,
        polynomial.eval_X, polynomial.eval_bit1, polynomial.eval_bit0, polynomial.eval_one],
      erw fin.mk_one, -- TODO whyyyy
      norm_num,
      rw (show (17 : (ℤ ⧸ ideal.span ({3} : set ℤ))) = ideal.quotient.mk _ 17, by simp),
      rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton],
      norm_num, }, },
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
  simp only [set.mem_set_of_eq, set.mem_union_eq, set.mem_image],
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
lemma class_group.mk0_span_singleton_eq_one {R : Type*} {K : Type*} [comm_ring R] [field K]
  [algebra R K] [is_fraction_ring R K] [is_domain R] [is_dedekind_domain R] {I : R} {h} :
  class_group.mk0 K ⟨ideal.span ({I} : set R), h⟩ = 1 :=
by simp

@[simp]
lemma class_group.mk0_top {R : Type*} {K : Type*} [comm_ring R] [field K]
  [algebra R K] [is_fraction_ring R K] [is_domain R] [is_dedekind_domain R] {h} :
  class_group.mk0 K ⟨(⊤ : ideal R), h⟩ = 1 :=
by simp

-- TODO please someone tell me the correct way to do this
@[simp]
lemma class_group.mk0_mul {R : Type*} {K : Type*} [comm_ring R] [field K]
  [algebra R K] [is_fraction_ring R K] [is_domain R] [is_dedekind_domain R] {I J : ideal R} {h} :
  class_group.mk0 K ⟨I * J, h⟩ = class_group.mk0 K ⟨I, by {rw [mem_non_zero_divisors_iff_ne_zero] at *, intro hh; apply h; rw hh, rw zero_mul}⟩
                          * class_group.mk0 K ⟨J, by {rw [mem_non_zero_divisors_iff_ne_zero] at *; intro hh; apply h; rw hh, rw mul_zero}⟩ :=
by simp only [set_like.coe_mk, fractional_ideal.coe_ideal_mul, mk0_apply, units.mk0_mul, quotient_group.coe_mul]

/-- the class group of `ℚ(√ -13)` consists of at most two elements. -/
theorem thirteen_class_group_eq
  (I : class_group (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13))) :
  I ∈ ({1, class_group.sqrt_2 (-13) (-13)} :
    finset (class_group ℤ[√ -13] (quad_ring ℚ 0 (-13)))) :=
begin
  simp only [finset.mem_insert, finset.mem_singleton],
  obtain ⟨⟨J, hJ0⟩, rfl, hJ⟩ := zsqrtneg13.exists_J' I,
  have hJ2 : J ∣ ideal.span {12}, -- TODO extract this whole calculation as lemma
  { simpa only [set_like.coe_mk, ideal.dvd_iff_le, ideal.span_singleton_le_iff] using hJ },
  rw show (12 : ℤ[√ -13]) = 3 * 2 * 2, by refl at hJ2, -- TODO norm_num fails??! maybe should ext first?
  rw ← ideal.span_singleton_mul_span_singleton at hJ2,
  rw ← ideal.span_singleton_mul_span_singleton at hJ2,
  rw [← sqrt_2_pow_two, pow_two, mul_assoc, mul_assoc] at hJ2,
  simp_rw ← set.mem_set_of_eq at hJ2,
  have : J ∈ {I : ideal ℤ[√ -13] | I ∣ ideal.span ({3} : set ℤ[√ -13]) * (↑(sqrt_2 (-13)) * (↑(sqrt_2 (-13)) * (↑(sqrt_2 (-13)) * ↑(sqrt_2 (-13)))))},
  { rwa set.mem_set_of_eq, },
  -- TODO simplify this with a prime pow version
  simp only [factors_prime_mul (gcd_monoid.prime_of_irreducible irred_three),
    factors_prime_mul (sqrt_2_prime (-13)),
    factors_prime (gcd_monoid.prime_of_irreducible irred_three),
    factors_prime (sqrt_2_prime (-13))] at this,
  simp only [ideal.one_eq_top, set.image_insert, ideal.mul_top, set.image_singleton,
    set.union_insert, set.union_singleton, set.insert_eq_of_mem, set.mem_insert_iff,
    eq_self_iff_true, true_or, set.mem_singleton_iff, or_true] at this,
  have helper : sqrt_2 (-13) * sqrt_2 (-13) = ⟨ideal.span ({2} : set ℤ[√ -13]),
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
  simp only [set_like.eta, class_group.mk0_mul, mul_one, one_mul, eq_self_iff_true, class_group.mk0_span_singleton_eq_one, or_true, true_or] {fail_if_unchanged := ff},
end

-- noncomputable instance thirteen_fintype : fintype (class_group (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13))) :=
-- class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible

lemma thirteen_univ_eq : finset.univ =
  ({1, class_group.sqrt_2 (-13) (-13)} : finset (class_group (quad_ring ℤ 0 (-13)) (quad_ring ℚ 0 (-13)))) :=
symm $ eq_top_iff.mpr $ λ I _, thirteen_class_group_eq I


lemma card_class_group_thirteen : fintype.card (class_group ℤ[√ -13] ℚ(√ -13)) = 2 :=
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
