import number_theory.assorted_lemmas
import ring_theory.norm
import ring_theory.ideal.norm
import linear_algebra.free_module.finite.basic
-- import number_theory.class_number_bound
.
-- TODO reorganise context menu
noncomputable theory
open_locale classical

section ideal_norm
namespace ideal
variables {R : Type*} [comm_ring R]

-- TODO this proof is very ugly
-- TODO can this be generalized to any multiplicative map?
-- TODO can this be generalized to any submodule not just ideals?
lemma span_norm_singleton_eq_span_singleton_norm {r : R} :
  span (algebra.norm ℤ '' ((span ({r} : set R) : ideal R) : set R)) =
  span {algebra.norm ℤ r} :=
begin
  have : ∀ x ∈ (algebra.norm ℤ : R →* ℤ) '' ↑(span ({r} : set R)), algebra.norm ℤ r ∣ x,
  { intros x hx,
    rw set.mem_image at hx,
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩,
    simp only [mem_span_singleton, set_like.mem_coe] at hx_h_left,
    exact map_dvd _ hx_h_left, },
  have : ∀ x ∈ span ((algebra.norm ℤ : R →* ℤ) '' ↑(span ({r} : set R))), algebra.norm ℤ r ∣ x,
  { intros x hx,
    apply submodule.span_induction hx this (dvd_zero _) (λ y z, dvd_add),
    intros a x ha,
    rw [algebra.id.smul_eq_mul],
    exact dvd_mul_of_dvd_right ha a, -- TODO should have a lemma dvd_smul_of_dvd_right?
  },
  apply le_antisymm,
  { erw submodule.le_span_singleton_iff,
    intros v hv,
    specialize this v hv,
    rw [dvd_iff_exists_eq_mul_left] at this,
    simp_rw eq_comm,
    simpa, },
  { erw submodule.span_singleton_le_iff_mem,
    exact submodule.subset_span (set.mem_image_of_mem _
      (submodule.subset_span (set.mem_singleton r))), },
end

-- TODO this might be useless
lemma coe_one : ((1 : ideal R) : set R) = set.univ :=
by simp [submodule.one_eq_span]
variables [is_domain R] [is_dedekind_domain R] [module.finite ℤ R] [module.free ℤ R]
-- this is a typeclassy way of saying that R is not a field

open ideal
/-
/-- The absolute norm of an ideal, as a multiplicative map from the set of ideals to the naturals -/
def abs_norm : ideal R →*₀ ℕ :=
{ to_fun := λ I, (ideal.norm ℤ I).nat_abs,
  map_zero' := by simp,
  map_one' := by simp,
  map_mul' := begin
    intros x y,
    obtain b := module.free.choose_basis ℤ R,
    rw [card_norm_eq_norm b, card_norm_eq_norm b, card_norm_eq_norm b, card_norm_mul b,
      nat.cast_mul, int.nat_abs_of_nat, int.nat_abs_mul, int.nat_abs_of_nat],
  end }

lemma abs_norm_def (I : ideal R) : abs_norm I = (ideal.norm ℤ I).nat_abs := rfl
--   int.nat_abs (submodule.is_principal.generator $ ideal.span (algebra.norm ℤ '' (I : set R))) :=
-- rfl
  -- abs_norm I = Sup ((λ r, (algebra.norm ℤ r).nat_abs) '' (I : set R)) := rfl
-/


end ideal
end ideal_norm
