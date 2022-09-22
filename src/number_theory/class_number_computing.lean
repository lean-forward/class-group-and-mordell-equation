import data.nat.squarefree
import data.int.sqrt
import number_theory.class_number.number_field
import number_theory.quad_ring.basic

/-!
# Showing the class group of `ℤ[√ d]` is nontrivial
-/

open_locale non_zero_divisors
open quad_ring
open_locale quad_ring

section to_mathlib

section

/-!
### The class group is independent of choice of fraction field or ring of integers
-/

open submodule

/-- This is `submodule.map_mul` where `g` satisfies the conditions of `alg_hom`
except it's semilinear. -/
protected lemma submodule.map_mulₛₗ {R R' A A'} [comm_semiring R] [comm_semiring R']
  [semiring A] [semiring A'] [algebra R A] [algebra R' A']
  (f : R →+* R') [ring_hom_surjective f]
  (g : A →ₛₗ[f] A') (hg : ∀ (x y : A), g (x * y) = g x * g y) (M N : submodule R A) :
  map g (M * N) = map g M * map g N :=
calc map g (M * N)
    = ⨆ (i : M), (N.map (algebra.lmul R A i)).map g : map_supr _ _
... = map g M * map g N  :
  begin
    apply congr_arg Sup,
    ext S,
    split; rintros ⟨y, hy⟩,
    { use [g y, mem_map.mpr ⟨y.1, y.2, rfl⟩],
      refine trans _ hy,
      ext,
      simp [hg] },
    { obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2,
      use [y', hy'],
      refine trans _ hy,
      ext,
      simp [fy_eq, hg] }
end

end

lemma ideal.span_eq_span_iff {R : Type*} [comm_ring R]
  {s t : set R} : ideal.span s = ideal.span t ↔ s ⊆ ideal.span t ∧ t ⊆ ideal.span s :=
le_antisymm_iff.trans (by simp only [ideal.span_le])

@[simp] lemma subgroup.comap_id {G : Type*} [group G] (G' : subgroup G) :
  subgroup.comap (monoid_hom.id _) G' = G' :=
by { ext, refl }

@[simp] lemma quotient_group.map_id_apply {G : Type*} [group G] (G' : subgroup G) [G'.normal]
  (h : G' ≤ subgroup.comap (monoid_hom.id _) G' := (subgroup.comap_id G').le) (x) :
  quotient_group.map G' G' (monoid_hom.id _) h x = x :=
begin
  refine quotient_group.induction_on' x (λ x, _),
  simp only [quotient_group.map_coe, monoid_hom.id_apply]
end

@[simp] lemma quotient_group.map_id {G : Type*} [group G] (G' : subgroup G) [G'.normal]
  (h : G' ≤ subgroup.comap (monoid_hom.id _) G' := (subgroup.comap_id G').le) :
  quotient_group.map G' G' (monoid_hom.id _) h = monoid_hom.id _ :=
monoid_hom.ext (quotient_group.map_id_apply G' h)

@[simp] lemma quotient_group.map_map {G H I : Type*} [group G] [group H] [group I]
  (G' : subgroup G) (H' : subgroup H) (I' : subgroup I)
  [G'.normal] [H'.normal] [I'.normal]
  (f : G →* H) (g : H →* I) (hf : G' ≤ subgroup.comap f H') (hg : H' ≤ subgroup.comap g I')
  (hgf : G' ≤ subgroup.comap (g.comp f) I' :=
    hf.trans ((subgroup.comap_mono hg).trans_eq (subgroup.comap_comap _ _ _))) (x : G ⧸ G') :
  quotient_group.map H' I' g hg (quotient_group.map G' H' f hf x) =
    quotient_group.map G' I' (g.comp f) hgf x :=
begin
  refine quotient_group.induction_on' x (λ x, _),
  simp only [quotient_group.map_coe, monoid_hom.comp_apply]
end

@[simp] lemma quotient_group.map_comp_map {G H I : Type*} [group G] [group H] [group I]
  (G' : subgroup G) (H' : subgroup H) (I' : subgroup I)
  [G'.normal] [H'.normal] [I'.normal]
  (f : G →* H) (g : H →* I) (hf : G' ≤ subgroup.comap f H') (hg : H' ≤ subgroup.comap g I')
  (hgf : G' ≤ subgroup.comap (g.comp f) I' :=
    hf.trans ((subgroup.comap_mono hg).trans_eq (subgroup.comap_comap _ _ _))) :
  (quotient_group.map H' I' g hg).comp (quotient_group.map G' H' f hf) =
    quotient_group.map G' I' (g.comp f) hgf :=
monoid_hom.ext (quotient_group.map_map G' H' I' f g hf hg hgf)

@[simp]
lemma mul_equiv.coe_monoid_hom_refl {M : Type*} [monoid M] :
  (mul_equiv.refl M : M →* M) = monoid_hom.id M :=
rfl

@[simp]
lemma mul_equiv.coe_monoid_hom_trans {M N P : Type*} [monoid M] [monoid N] [monoid P]
  (e₁ : M ≃* N) (e₂ : N ≃* P) :
  (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ :=
rfl

@[simp]
lemma mul_equiv.self_trans_symm {M N : Type*} [monoid M] [monoid N] (e : M ≃* N) :
  e.trans e.symm = mul_equiv.refl _ :=
by { ext, exact e.symm_apply_apply _ }

@[simp]
lemma mul_equiv.symm_trans_self {M N : Type*} [monoid M] [monoid N] (e : M ≃* N) :
  e.symm.trans e = mul_equiv.refl _ :=
by { ext, exact e.apply_symm_apply _ }

/-- `quotient_group.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
given that `e` maps `G` to `H`. -/
def quotient_group.congr {G H : Type*} [group G] [group H] (G' : subgroup G) (H' : subgroup H)
  [G'.normal] [H'.normal] (e : G ≃* H) (he : G'.map ↑e = H') : G ⧸ G' ≃* H ⧸ H' :=
{ to_fun := quotient_group.map G' H' ↑e (he ▸ G'.le_comap_map e),
  inv_fun := quotient_group.map H' G' ↑e.symm (he ▸ (G'.map_equiv_eq_comap_symm e).le),
  left_inv := λ x, by rw quotient_group.map_map; -- `simp` doesn't like this lemma...
    simp only [← mul_equiv.coe_monoid_hom_trans, mul_equiv.self_trans_symm,
        mul_equiv.coe_monoid_hom_refl, quotient_group.map_id_apply],
  right_inv := λ x, by rw quotient_group.map_map; -- `simp` doesn't like this lemma...
    simp only [← mul_equiv.coe_monoid_hom_trans, mul_equiv.symm_trans_self,
        mul_equiv.coe_monoid_hom_refl, quotient_group.map_id_apply],
  .. quotient_group.map G' H' ↑e (he ▸ G'.le_comap_map e) }

/-- `is_localization.map` bundled as a semilinear map. -/
@[simps]
noncomputable def is_localization.map_semilinear {R S} (Rₘ Sₙ : Type*)
  [comm_ring R] [comm_ring S] (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  {F : Type*} [ring_hom_class F R S] (f : F) (hf : M ≤ N.comap f) : Rₘ →ₛₗ[(f : R →+* S)] Sₙ :=
{ to_fun := is_localization.map Sₙ (f : R →+* S) hf,
  map_smul' := λ r x, is_localization.map_smul _ _ _,
  .. is_localization.map Sₙ (f : R →+* S) hf }

-- Should be a congr lemma but can't because `@[congr]` doesn't
-- understand `coe_fn`
lemma is_localization.map_semilinear_congr {R S Rₘ Sₙ : Type*} [comm_ring R] [comm_ring S]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  {F : Type*} [ring_hom_class F R S] (f g : F) (hf : M ≤ N.comap f) (hg : M ≤ N.comap g)
  (h : f = g) (x y : Rₘ) (hxy : x = y) :
  (is_localization.map_semilinear Rₘ Sₙ M N f hf) x =
    (is_localization.map_semilinear Rₘ Sₙ M N g hg) y :=
by subst h; subst hxy; refl

@[simp] lemma is_localization.map_semilinear_eq {R S Rₘ Sₙ : Type*} [comm_ring R] [comm_ring S]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  {F : Type*} [ring_hom_class F R S] (f : F) (hf : M ≤ N.comap f) (x : R) :
  is_localization.map_semilinear Rₘ Sₙ M N f hf (algebra_map R Rₘ x) = algebra_map S Sₙ (f x) :=
is_localization.map_eq _ _

@[simp] lemma is_localization.map_semilinear_mul {R S Rₘ Sₙ : Type*} [comm_ring R] [comm_ring S]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  {F : Type*} [ring_hom_class F R S] (f : F) (hf : M ≤ N.comap f) (x y : Rₘ) :
  is_localization.map_semilinear Rₘ Sₙ M N f hf (x * y) =
    is_localization.map_semilinear Rₘ Sₙ M N f hf x *
    is_localization.map_semilinear Rₘ Sₙ M N f hf y :=
by simp only [is_localization.map_semilinear, linear_map.coe_mk, map_mul]

@[simp] lemma is_localization.map_semilinear_comp_apply {R S T Rₘ Sₙ Tₚ : Type*}
  [comm_ring R] [comm_ring S] [comm_ring T]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  (P : submonoid T) [comm_ring Tₚ] [algebra T Tₚ] [is_localization P Tₚ]
  {F : Type*} [ring_hom_class F R S] (f : F) (hf : M ≤ N.comap f)
  {G : Type*} [ring_hom_class G S T] (g : G) (hg : N ≤ P.comap g)
  {GF : Type*} [ring_hom_class GF R T] (gf : GF) (hgf : M ≤ P.comap gf)
  [ring_hom_comp_triple (f : R →+* S) (g : S →+* T) gf]
  (x : Rₘ) :
  (is_localization.map_semilinear _ Tₚ M P gf hgf : Rₘ →ₛₗ[_] _) x =
    is_localization.map_semilinear _ Tₚ N P g hg
      (is_localization.map_semilinear _ Sₙ M N f hf x) :=
begin
  simp only [is_localization.map_semilinear, linear_map.coe_mk, linear_map.coe_comp],
  -- Help the elaborator with inserting the coercions
  convert fun_like.ext_iff.mp
    (@is_localization.map_comp_map R _ _ Rₘ _ _ S _ _ f _ Sₙ _ hf _ _ T _ _ Tₚ _ _ _ g hg).symm x,
  exact ring_hom_comp_triple.comp_eq.symm
end

@[simp] lemma is_localization.map_semilinear_comp {R S T Rₘ Sₙ Tₚ : Type*}
  [comm_ring R] [comm_ring S] [comm_ring T]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  (P : submonoid T) [comm_ring Tₚ] [algebra T Tₚ] [is_localization P Tₚ]
  {F : Type*} [ring_hom_class F R S] (f : F) (hf : M ≤ N.comap f)
  {G : Type*} [ring_hom_class G S T] (g : G) (hg : N ≤ P.comap g)
  {GF : Type*} [ring_hom_class GF R T] (gf : GF) (hgf : M ≤ P.comap gf)
  [ring_hom_comp_triple (f : R →+* S) (g : S →+* T) gf] :
  (is_localization.map_semilinear _ Tₚ M P gf hgf : Rₘ →ₛₗ[_] _) =
    (is_localization.map_semilinear _ Tₚ N P g hg).comp
      (is_localization.map_semilinear _ Sₙ M N f hf) :=
begin
  ext x,
  apply is_localization.map_semilinear_comp_apply
end

@[simp] lemma is_localization.map_semilinear_id_apply {R Rₘ : Type*}
  [comm_ring R]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (x : Rₘ) :
  (is_localization.map_semilinear Rₘ Rₘ M M (ring_hom.id R)
      (submonoid.comap_id M).le : Rₘ →ₛₗ[_] _) x =
    x :=
is_localization.map_id x (submonoid.comap_id M).le

@[simp] lemma fractional_ideal.mem_mk {R Rₘ : Type*} [comm_ring R] {M : submonoid R} [comm_ring Rₘ]
  [algebra R Rₘ] {S : submodule R Rₘ} {h : is_fractional M S} {x} :
  x ∈ (show fractional_ideal M Rₘ, from ⟨S, h⟩) ↔ x ∈ S :=
iff.rfl

/-- If `f : R →+* S` maps `M : submonoid R` to `N : submonoid S`, then the fractional ideals
at `M` can be mapped to those at `N`. -/
@[simps apply]
noncomputable def fractional_ideal.map_base {R S Rₘ Sₙ : Type*} [comm_ring R] [comm_ring S]
  (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  {F : Type*} [ring_hom_class F R S] (f : F) (hf : function.surjective f) (hfM : M ≤ N.comap f) :
  fractional_ideal M Rₘ →+* fractional_ideal N Sₙ :=
{ to_fun := λ I, ⟨by haveI : ring_hom_surjective (f : R →+* S) := ⟨hf⟩;
    exact submodule.map (is_localization.map_semilinear Rₘ Sₙ M N f hfM) (I : submodule R Rₘ),
    begin
      obtain ⟨a, haM, ha⟩ := I.2,
      refine ⟨f a, hfM haM, _⟩,
      simp only [submodule.mem_map, fractional_ideal.mem_coe, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂],
      intros b hb,
      obtain ⟨ab, hab⟩ := ha b hb,
      use f ab,
      -- Work around the `↑f` because `linear_map.map_smulₛₗ` is non-generic in `f`.
      rw [← ring_hom.coe_coe f, ← linear_map.map_smulₛₗ, ← hab, is_localization.map_semilinear_eq,
          ring_hom.coe_coe f]
    end⟩,
  map_zero' := by ext; simp only [submodule.map_bot, fractional_ideal.coe_zero, submodule.mem_bot,
    fractional_ideal.mem_zero_iff, fractional_ideal.mem_mk],
  -- TODO: do the following lines with just `fractional_ideal.ext`
  map_add' := λ I J, fractional_ideal.coe_to_submodule_injective $
    by simp only [fractional_ideal.coe_add, submodule.map_sup, submodule.add_eq_sup, fractional_ideal.coe_mk],
  map_one' := fractional_ideal.coe_to_submodule_injective $ begin
    ext,
    simp only [fractional_ideal.coe_mk, fractional_ideal.coe_one, submodule.mem_map,
      submodule.mem_one, exists_exists_eq_and],
    split,
    { rintros ⟨a, rfl⟩,
      simp only [is_localization.map_semilinear_eq, exists_apply_eq_apply] },
    { rintros ⟨a, rfl⟩,
      obtain ⟨x, rfl⟩ := hf a,
      simp only [is_localization.map_semilinear_eq, exists_apply_eq_apply] },
  end,
  map_mul' := λ I J, fractional_ideal.coe_to_submodule_injective $ begin
    simp only [fractional_ideal.coe_mul, fractional_ideal.coe_mk],
    apply submodule.map_mulₛₗ,
    apply is_localization.map_semilinear_mul
  end }

universes u v u' v'
/-- If `e : R ≃+* S` maps `M : submonoid R` to `N : submonoid S`, then the fractional ideals
at `M` are isomorphic to those at `N`. -/
@[simps]
noncomputable def fractional_ideal.congr {R : Type u} {S : Type v} (Rₘ : Type u') (Sₙ : Type v')
  [comm_ring R] [comm_ring S] (M : submonoid R) [comm_ring Rₘ] [algebra R Rₘ] [is_localization M Rₘ]
  (N : submonoid S) [comm_ring Sₙ] [algebra S Sₙ] [is_localization N Sₙ]
  (e : R ≃+* S) (he : M.map e = N) : fractional_ideal M Rₘ ≃+* fractional_ideal N Sₙ :=
{ to_fun := fractional_ideal.map_base M N e e.surjective (submonoid.map_le_iff_le_comap.mp he.le),
  inv_fun := fractional_ideal.map_base N M e.symm e.symm.surjective (submonoid.map_le_iff_le_comap.mp
    (eq.le $ begin
      rw ← he,
      refine (submonoid.map_map M (e.symm : S →* R) (e : R →* S)).trans _,
      convert submonoid.map_id _,
      ext,
      exact e.symm_apply_apply x
    end)),
  -- TODO: the next lines should be doable using `fractional_ideal.ext`
  left_inv := λ I, fractional_ideal.coe_to_submodule_injective $ begin
    simp only [fractional_ideal.map_base_apply, fractional_ideal.coe_mk],
    haveI : ring_hom_surjective (e : R →+* S) := ⟨e.surjective⟩,
    haveI : ring_hom_surjective (e.symm : S →+* R) := ⟨e.symm.surjective⟩,
    haveI : ring_hom_comp_triple (e : R →+* S) (e.symm : S →+* R) (ring_hom.id R) :=
      ⟨e.symm_to_ring_hom_comp_to_ring_hom⟩,
    haveI : ring_hom_comp_triple (e.symm : S →+* R) (e : R →+* S) (ring_hom.id S) :=
      ⟨e.to_ring_hom_comp_symm_to_ring_hom⟩,
    -- Come on, Lean!
    calc submodule.map (is_localization.map_semilinear Sₙ Rₘ N M e.symm _) (submodule.map (is_localization.map_semilinear Rₘ Sₙ M N e _) ↑I)
        = submodule.map ((is_localization.map_semilinear Sₙ Rₘ N M e.symm _).comp (is_localization.map_semilinear Rₘ Sₙ M N e _)) ↑I : (submodule.map_comp (is_localization.map_semilinear Rₘ Sₙ M N e _) (is_localization.map_semilinear Sₙ Rₘ N M e.symm _) _).symm
    ... = submodule.map linear_map.id ↑I : _
    ... = ↑I : submodule.map_id _,
    congr,
    ext x,
    calc (is_localization.map_semilinear Sₙ Rₘ N M e.symm _).comp
            (is_localization.map_semilinear Rₘ Sₙ M N e _) x
        = is_localization.map_semilinear Rₘ Rₘ M M (ring_hom.id R) _ x :
      (is_localization.map_semilinear_comp_apply M N M e _ e.symm _ _ _ x).symm
    ... = x : is_localization.map_semilinear_id_apply M x
    ... = linear_map.id x : (linear_map.id_apply x).symm
  end,
  right_inv := λ I, fractional_ideal.coe_to_submodule_injective $ begin
    simp only [fractional_ideal.map_base_apply, fractional_ideal.coe_mk],
    haveI : ring_hom_surjective (e : R →+* S) := ⟨e.surjective⟩,
    haveI : ring_hom_surjective (e.symm : S →+* R) := ⟨e.symm.surjective⟩,
    haveI : ring_hom_comp_triple (e : R →+* S) (e.symm : S →+* R) (ring_hom.id R) :=
      ⟨e.symm_to_ring_hom_comp_to_ring_hom⟩,
    haveI : ring_hom_comp_triple (e.symm : S →+* R) (e : R →+* S) (ring_hom.id S) :=
      ⟨e.to_ring_hom_comp_symm_to_ring_hom⟩,
    calc submodule.map (is_localization.map_semilinear Rₘ Sₙ M N e _) (submodule.map (is_localization.map_semilinear Sₙ Rₘ N M e.symm _) ↑I)
        = submodule.map ((is_localization.map_semilinear Rₘ Sₙ M N e _).comp (is_localization.map_semilinear Sₙ Rₘ N M e.symm _)) ↑I : (submodule.map_comp (is_localization.map_semilinear Sₙ Rₘ N M e.symm _) (is_localization.map_semilinear Rₘ Sₙ M N e _) _).symm
    ... = submodule.map linear_map.id ↑I : _
    ... = ↑I : submodule.map_id _,
    congr,
    ext x,
    calc (is_localization.map_semilinear Rₘ Sₙ M N e _).comp (is_localization.map_semilinear Sₙ Rₘ N M e.symm _) x
        = is_localization.map_semilinear Sₙ Sₙ N N (ring_hom.id S) _ x :
      (is_localization.map_semilinear_comp_apply N M N e.symm _ e _ _ _ x).symm
    ... = x : is_localization.map_semilinear_id_apply N x
    ... = linear_map.id x : (linear_map.id_apply x).symm
  end,
  .. fractional_ideal.map_base M N e e.surjective _ }

-- TODO: the existence of this instance helps the elaborator unify quotient_group.group with comm_group.to_group
instance (R K : Type*) [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K] :
  group (class_group R K) := quotient_group.quotient.group _

@[simp] lemma map_non_zero_divisors {R S : Type*} [comm_ring R] [is_domain R] [comm_ring S] [is_domain S]
  (e : R ≃+* S) : submonoid.map e R⁰ = S⁰ :=
begin
  ext,
  simp only [submonoid.mem_map],
  split,
  { rintro ⟨x, hx, rfl⟩,
    exact map_mem_non_zero_divisors e e.injective hx },
  { intro hx,
    exact ⟨e.symm x, map_mem_non_zero_divisors e.symm e.symm.injective hx, e.apply_symm_apply x⟩ }
end

lemma units_map_equiv_congr_to_principal_ideal {R S : Type*} (K L : Type*)
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S]
  [field K] [field L] [algebra R K] [is_fraction_ring R K] [algebra S L] [is_fraction_ring S L]
  (e : R ≃+* S) (x : Kˣ) :
  (units.map_equiv ↑(fractional_ideal.congr K L R⁰ S⁰ e (map_non_zero_divisors e))) (to_principal_ideal R K x) =
    to_principal_ideal S L (units.map_equiv ↑(is_localization.ring_equiv_of_ring_equiv K L e (map_non_zero_divisors e)) x) :=
begin
  ext : 1,
  rw coe_to_principal_ideal,
  show fractional_ideal.congr K L R⁰ S⁰ e _ (to_principal_ideal R K x) = _,
 rw coe_to_principal_ideal,
 apply fractional_ideal.coe_to_submodule_injective,
 simp only [is_localization.ring_equiv_of_ring_equiv_apply, fractional_ideal.map_base_apply,
   ring_equiv.coe_to_mul_equiv, fractional_ideal.coe_span_singleton,
   fractional_ideal.congr_apply, fractional_ideal.coe_mk, submodule.map_span,
   set.image_singleton, is_localization.map_semilinear_apply],
  refl
end

/-- The class group of `R` in `K` is isomorphic to that of `S` in `L`,
if `R` is isomorphic to `S`. -/
noncomputable def class_group.equiv {R : Type u} {S : Type v} (K : Type u') (L : Type v')
  [comm_ring R] [is_domain R] [comm_ring S] [is_domain S]
  [field K] [field L] [algebra R K] [is_fraction_ring R K] [algebra S L] [is_fraction_ring S L]
  (e : R ≃+* S) : class_group R K ≃* class_group S L :=
quotient_group.congr (to_principal_ideal R K).range (to_principal_ideal S L).range
  (units.map_equiv ↑(fractional_ideal.congr K L R⁰ S⁰ e (map_non_zero_divisors e))) $
  by { rw [monoid_hom.range_eq_map, subgroup.map_map, monoid_hom.range_eq_map],
       ext,
       simp only [subgroup.mem_map, subgroup.mem_top, exists_prop, true_and,
          monoid_hom.comp_apply],
       let e' : K ≃* L := is_localization.ring_equiv_of_ring_equiv K L e (map_non_zero_divisors e),
       split; rintro ⟨x, rfl⟩,
       { exact ⟨units.map_equiv e' x, (units_map_equiv_congr_to_principal_ideal K L e x).symm⟩ },
       { refine ⟨units.map_equiv e'.symm x, (units_map_equiv_congr_to_principal_ideal K L e _).trans _⟩,
         congr, ext : 1,
         exact mul_equiv.apply_symm_apply _ x } }

end to_mathlib

section to_mathlib

/-- The class number of a number field does not depend on a choice of ring of integers. -/
theorem number_field.class_number_eq (R : Type*) (K : Type*) [comm_ring R] [is_domain R]
  [field K] [algebra R K] [is_fraction_ring R K] [number_field K] [is_integral_closure R ℤ K] :
  number_field.class_number K = @fintype.card (class_group R K)
    (class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible) :=
begin
  letI : fintype (class_group R K) :=
    class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible,
  unfold number_field.class_number,
  refine fintype.card_eq.mpr ⟨(class_group.equiv K K _).to_equiv⟩,
  exact number_field.ring_of_integers.equiv _,
end

end to_mathlib

open_locale pointwise

section to_mathlib

@[simp]
lemma set.insert_mul {M : Type*} [has_mul M]
  (s t : set M) (x : M) : insert x s * t = x • t ∪ s * t :=
by rw [set.insert_eq, set.union_mul, set.singleton_mul]; refl
@[simp]
lemma set.mul_insert {M : Type*} [comm_monoid M]
  (s t : set M) (x : M) : s * insert x t = x • s ∪ s * t :=
by rw [set.insert_eq, set.mul_union, set.mul_singleton];
  -- TODO: clean me!
  congr' 2; ext; apply mul_comm

@[simp]
lemma set.smul_set_insert {M : Type*} [comm_monoid M]
  (x y : M) (s : set M) : x • insert y s = insert (x * y) (x • s) :=
by rw [set.insert_eq, set.smul_set_union, set.smul_set_singleton, set.insert_eq]; refl

@[simp]
lemma set.image_insert {α β : Type*} (f : α → β) (x : α) (s : set α) :
  f '' (insert x s) = insert (f x) (f '' s) :=
by simp only [set.insert_eq, set.image_union, set.image_singleton]

lemma ideal.span_eq_bot_iff_subset {α : Type*} [comm_semiring α] {S : set α} :
  ideal.span S = ⊥ ↔ S ⊆ {0} :=
ideal.span_eq_bot.trans set.subset_singleton_iff.symm

lemma set.not_subset_singleton_iff {α : Type*} {s : set α} {x : α} :
  ¬ (s ⊆ {x}) ↔ s ≠ ∅ ∧ s ≠ {x} :=
by rw [set.subset_singleton_iff_eq, not_or_distrib]

lemma ideal.span_ne_bot_iff {α : Type*} [comm_semiring α] {S : set α} :
  ideal.span S ≠ ⊥ ↔ (S.nonempty ∧ S ≠ {0}) :=
by simp only [ne.def, ideal.span_eq_bot_iff_subset, set.not_subset_singleton_iff,
              ← set.ne_empty_iff_nonempty]

@[simp] lemma set.ne_singleton_of_ne {α : Type*} {s : set α} {x y : α}
  (hxs : x ∈ s) (hxy : x ≠ y) : s ≠ {y} :=
by { contrapose! hxy, rw hxy at hxs, exact set.eq_of_mem_singleton hxs }

end to_mathlib

section basic

@[simp] lemma coe_dvd_mk {R : Type*} [comm_ring R] {n a b x y : R} :
  ↑n ∣ (⟨x, y⟩ : quad_ring R a b) ↔ n ∣ x ∧ n ∣ y :=
begin
  split,
  { rintro ⟨⟨da, db⟩, hd⟩,
    simp only [quad_ring.ext_iff, add_zero, int.cast_id, quad_ring.mul_b2, zero_mul,
      quad_ring.mul_b1, quad_ring.coe_b1, zero_add, quad_ring.coe_b2, mul_zero] at hd,
    exact ⟨⟨_, hd.1⟩, ⟨_, hd.2⟩⟩ },
  { rintro ⟨⟨da, hda⟩, ⟨db, hdb⟩⟩,
    refine ⟨⟨da, db⟩, _⟩,
    ext; simp [hda, hdb] }
end

instance {b : ℚ} [fact $ ¬ is_square b] : number_field (quad_ring ℚ 0 b) :=
{ to_finite_dimensional := quad_ring.finite_dimensional 0 b }

end basic

/-- The ideal `⟨2⟩` in ℤ[√ d] is a square if `d % 4 = 3`.  -/
lemma exists_sqrt_2_mod_three (d : ℤ) (hd : d % 4 = 3) :
  (ideal.span ({⟨1, 1⟩, 2} : set (quad_ring ℤ 0 d)))^2 = ideal.span {2} :=
begin
  have : (1 + d) % 4 = 0 := by { rw int.add_mod, norm_num [hd] },
  rw ← int.dvd_iff_mod_eq_zero at this,

  -- We show a very explicit equality by checking the inclusion of the span on both sides.
  simp only [pow_two, ideal.span_mul_span', set.insert_mul, set.mul_insert, set.singleton_mul,
    set.mul_singleton, set.smul_set_singleton, set.smul_set_insert, smul_eq_mul,
    set.insert_union, set.singleton_union, set.image_insert, set.image_singleton,
    set.insert_eq_of_mem, set.mem_insert_iff, eq_self_iff_true, true_or],
  rw [show (⟨1, 1⟩ : quad_ring ℤ 0 d) * (⟨ 1, 1 ⟩) = ⟨1 + d, 2⟩, by quad_ring.calc_tac,
      show (⟨1, 1⟩ : quad_ring ℤ 0 d) * 2 = ⟨2, 2⟩, by quad_ring.calc_tac,
      show (2 : quad_ring ℤ 0 d) * 2 = 4, by norm_num],
  refine ideal.span_eq_span_iff.mpr ⟨_, _⟩;
    simp only [set.insert_subset, set.singleton_subset_iff, ideal.mem_span_singleton,
      set_like.mem_coe],
  refine ⟨_, _, _⟩; refine coe_dvd_mk.mpr ⟨_, _⟩,
  { calc 2 ∣ 4 : by norm_num
       ... ∣ 1 + d : this },
  { refl },
  { refl },
  { refl },
  { exact (show (2 : ℤ) ∣ 4, by norm_num) },
  { exact (show (2 : ℤ) ∣ 0, by norm_num) },
  { obtain ⟨k, hk⟩ := this,
    simp only [ideal.mem_span_insert, ideal.mem_span_singleton, exists_prop],
    refine ⟨-1, _, ⟨1, _, ⟨k, rfl⟩, rfl⟩, _⟩,
    rw hk,
    ext; simp },
end

/-- The ideal `⟨2⟩` in ℤ[√ d] is a square if `d % 4 = 2`.  -/
lemma exists_sqrt_2_mod_two (d : ℤ) (hd : d % 4 = 2) :
  (ideal.span ({⟨0, 1⟩, 2} : set (quad_ring ℤ 0 d)))^2 = ideal.span {2} :=
begin
  have : (2 + d) % 4 = 0 := by { rw int.add_mod, norm_num [hd] },
  rw ← int.dvd_iff_mod_eq_zero at this,

  -- We show a very explicit equality by checking the inclusion of the span on both sides.
  simp only [pow_two, ideal.span_mul_span', set.insert_mul, set.mul_insert, set.singleton_mul,
    set.mul_singleton, set.smul_set_singleton, set.smul_set_insert, smul_eq_mul,
    set.insert_union, set.singleton_union, set.image_insert, set.image_singleton,
    set.insert_eq_of_mem, set.mem_insert_iff, eq_self_iff_true, true_or],
  rw [show (⟨0, 1⟩ : quad_ring ℤ 0 d) * (⟨ 0, 1 ⟩) = ⟨d, 0⟩, by quad_ring.calc_tac,
      show (⟨0, 1⟩ : quad_ring ℤ 0 d) * 2 = ⟨0, 2⟩, by quad_ring.calc_tac,
      show (2 : quad_ring ℤ 0 d) * 2 = 4, by norm_num],
  refine ideal.span_eq_span_iff.mpr ⟨_, _⟩;
    simp only [set.insert_subset, set.singleton_subset_iff, ideal.mem_span_singleton,
      set_like.mem_coe],
  refine ⟨_, _, _⟩; refine coe_dvd_mk.mpr ⟨_, _⟩,
  { have := calc 2 ∣ 4 : by norm_num
       ... ∣ 2 + d : this,
    simpa },
  { exact dvd_zero _, },
  { exact dvd_zero _, },
  { refl },
  { exact (show (2 : ℤ) ∣ 4, by norm_num) },
  { exact (show (2 : ℤ) ∣ 0, by norm_num) },
  { obtain ⟨k, hk⟩ := this,
    simp only [ideal.mem_span_insert, ideal.mem_span_singleton, exists_prop],
    refine ⟨-1, _, ⟨0, _, ⟨k, rfl⟩, rfl⟩, _⟩,
    rw_mod_cast ← hk,
    ext; simp },
end

lemma norm_ne_two {d : ℤ} (hd2 : d < -2)
  (x : quad_ring ℤ 0 d) : algebra.norm ℤ x ≠ 2 :=
begin
  rw quad_ring.norm_eq,
  simp only [zero_mul, add_zero],
  by_cases hb2 : x.b2 = 0,
  { simp only [hb2, pow_two, mul_zero, sub_zero],
    have : ¬ is_square (2 : ℤ) :=
      (int.prime_iff_nat_abs_prime.mpr $ by norm_num).irreducible.not_is_square,
    rw [is_square, not_exists] at this,
    exact ne.symm (this x.b1) },
  { have hb2 : 0 < x.b2^2 := (sq_pos_iff _).mpr hb2,
    refine ne_of_gt _,
    calc 2 < -d : by linarith
       ... ≤ - d * x.b2^2 : by nlinarith
       ... ≤ x.b1^2 - d * x.b2^2 : by nlinarith }
end

/-- In `ℤ[√ d]`, if `d < -2`, the square root of the ideal ⟨2⟩ is not principal. -/
lemma not_principal_of_sq_eq_two {d : ℤ} (hd2 : d < -2)
  (I : ideal (quad_ring ℤ 0 d)) (h : I^2 = ideal.span {2}) :
  ¬ I.is_principal :=
begin
  rintro ⟨x, rfl⟩,
  rw [pow_two, ideal.submodule_span_eq, ideal.span_singleton_mul_span_singleton] at h,
  obtain ⟨a, ha⟩ := ideal.span_singleton_le_span_singleton.mp h.le,
  obtain ⟨b, hb⟩ := ideal.span_singleton_le_span_singleton.mp h.ge,
  rw ha at hb,
  apply_fun algebra.norm ℤ at ha hb,
  have hy : algebra.norm ℤ (2 : quad_ring ℤ 0 d) = 2^2 := quad_ring.norm_coe 2,
  simp only [map_mul, hy, mul_assoc] at ha hb,
  have : algebra.norm ℤ a = 1,
  { cases mul_right_eq_self₀.mp hb.symm with hb hb, swap,
    { norm_num at hb },
    cases int.is_unit_eq_one_or (is_unit_of_mul_eq_one _ _ hb) with hb hb,
    { assumption },
    { have := quad_ring.norm_nonneg _ a; linarith } },
  rw [this, mul_one, ← pow_two, sq_eq_sq (quad_ring.norm_nonneg _ x)] at ha,
  exact norm_ne_two hd2 x ha,
  repeat { linarith }
end

lemma is_not_principal_mod_three {d : ℤ} (hd : d % 4 = 3) (hd2 : d < -2) :
  ¬ submodule.is_principal (ideal.span ({⟨1, 1⟩, 2} : set (quad_ring ℤ 0 d))) :=
not_principal_of_sq_eq_two hd2 _ (exists_sqrt_2_mod_three d hd)

lemma is_not_principal_mod_two {d : ℤ} (hd : d % 4 = 2) (hd2 : d < -2) :
  ¬ submodule.is_principal (ideal.span ({⟨0, 1⟩, 2} : set (quad_ring ℤ 0 d))) :=
not_principal_of_sq_eq_two hd2 _ (exists_sqrt_2_mod_two d hd)

 -- `d` is a free variable so this can't be an instance
local attribute [instance] quad_ring.fact_not_square'_of_eq_two_or_three_mod_four

/-- `sqrt_2` is the square root of the ideal `⟨2⟩` of `ℤ[√ d]`, when `d % 4 ∈ {2, 3}`. -/
def sqrt_2 (d : ℤ) [hd : fact $ d % 4 = 2 ∨ d % 4 = 3] : (ideal (quad_ring ℤ 0 d))⁰ :=
if d % 4 = 2 then
  ⟨ideal.span ({⟨0, 1⟩, 2} : set (quad_ring ℤ 0 d)),
    mem_non_zero_divisors_of_ne_zero (ideal.span_ne_bot_iff.mpr ⟨set.insert_nonempty _ _,
      set.ne_singleton_of_ne (set.mem_insert_of_mem _ (set.mem_singleton 2)) two_ne_zero'⟩)⟩
else
  ⟨ideal.span ({⟨1, 1⟩, 2} : set (quad_ring ℤ 0 d)),
    mem_non_zero_divisors_of_ne_zero (ideal.span_ne_bot_iff.mpr ⟨set.insert_nonempty _ _,
      set.ne_singleton_of_ne (set.mem_insert_of_mem _ (set.mem_singleton 2)) two_ne_zero'⟩)⟩

lemma sqrt_2_pow_two (d : ℤ) [hd : fact $ d % 4 = 2 ∨ d % 4 = 3] :
  ((sqrt_2 d)^2 : ideal (quad_ring ℤ 0 d)) = ideal.span {2} :=
begin
  rw sqrt_2,
  split_ifs,
  { simp [exists_sqrt_2_mod_two d h], },
  { simp [exists_sqrt_2_mod_three d (hd.out.resolve_left h)], },
end

/-- `class_group.sqrt_2` is the square root of `⟨2⟩` in the ideal class group of `ℚ(√ d')`,
when `d % 4 ∈ {2, 3}`. -/
protected noncomputable def class_group.sqrt_2 (d : ℤ) (d' : ℚ) [fact (algebra_map ℤ ℚ d = d')]
  [hd : fact $ d % 4 = 2 ∨ d % 4 = 3] [fact $ squarefree d] :
  class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d') :=
class_group.mk0 _ (sqrt_2 d)

-- TODO a version of this for d = -2 and -1 saying that the order is 1
lemma order_of_sqrt2 {d : ℤ} (d' : ℚ) [fact (algebra_map ℤ ℚ d = d')]
  [hd : fact $ d % 4 = 2 ∨ d % 4 = 3] [fact $ squarefree d]
  (hd2 : d < -2) : order_of (class_group.sqrt_2 d d') = 2 :=
begin
  refine order_of_eq_prime _ _,
  { rw [class_group.sqrt_2, sqrt_2],
    split_ifs;
    simp_rw ← map_pow,
    { refine (class_group.mk0_eq_one_iff _).mpr _,
      simp only [exists_sqrt_2_mod_two d h],
      exact ⟨⟨2, rfl⟩⟩ },
    { refine (class_group.mk0_eq_one_iff _).mpr _,
      simp only [exists_sqrt_2_mod_three d (hd.out.resolve_left h)],
      exact ⟨⟨2, rfl⟩⟩ }, },
  { rw [ne.def, class_group.sqrt_2, sqrt_2],
    split_ifs; erw [class_group.mk0_eq_one_iff],
    exact is_not_principal_mod_two h hd2,
    exact is_not_principal_mod_three (hd.out.resolve_left h) hd2, },
end

theorem two_dvd_class_number (d : ℤ) (d' : ℚ) [hd : fact $ d % 4 = 2 ∨ d % 4 = 3]
  [fact $ squarefree d]
  (hd2 : d < -2) [hdd' : fact $ algebra_map ℤ ℚ d = d'] :
  2 ∣ number_field.class_number (quad_ring ℚ 0 d') :=
begin
  letI : fintype (class_group (quad_ring ℤ 0 d) (quad_ring ℚ 0 d')) :=
    class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible,
  rw [← order_of_sqrt2 d' hd2, number_field.class_number_eq (quad_ring ℤ 0 d) (quad_ring ℚ 0 d')],
  exact order_of_dvd_card_univ,
end

instance : fact $ ¬ is_square (-5 : ℤ) :=
⟨(int.prime_iff_nat_abs_prime.mpr $ by norm_num).irreducible.not_is_square⟩

theorem class_group_nontrivial :
  nontrivial (class_group (quad_ring ℤ 0 (-5)) (quad_ring ℚ 0 (-5))) :=
begin
  haveI : fact (algebra_map ℤ ℚ (-5) = (-5)) := ⟨by simp⟩,
  haveI : fact ((-5 : ℤ) % 4 = 2 ∨ (-5 : ℤ) % 4 = 3) := ⟨by norm_num⟩,
  haveI : fact (squarefree (-5 : ℤ)) := ⟨by norm_num [int.squarefree_iff_squarefree_nat_abs]⟩,
  haveI : is_dedekind_domain (quad_ring ℤ 0 (-5)) :=
    is_integral_closure.is_dedekind_domain ℤ ℚ (quad_ring ℚ 0 (-5)) _,
  letI : fintype (class_group (quad_ring ℤ 0 (-5)) (quad_ring ℚ 0 (-5))) :=
    class_group.fintype_of_admissible_of_finite ℚ _ absolute_value.abs_is_admissible,
  rw [← fintype.one_lt_card_iff_nontrivial,
      ← number_field.class_number_eq (quad_ring ℤ 0 (-5)) (quad_ring ℚ 0 (-5))],
  have := nat.le_of_dvd _ (two_dvd_class_number (-5) (-5) (by norm_num)),
  { linarith },
  unfold number_field.class_number,
  rw fintype.card_pos_iff,
  exact has_one.nonempty,
end
