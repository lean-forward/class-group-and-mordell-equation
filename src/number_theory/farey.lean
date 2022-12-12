import data.real.basic
import order.interval
import order.lattice
import topology.algebra.order.compact
import topology.instances.real
import data.nat.factorial.basic
import data.int.interval
import tactic.slim_check
-- import number_theory.geometry_of_numbers
import measure_theory.measure.haar
import linear_algebra.finite_dimensional
import analysis.normed_space.pointwise
import measure_theory.group.pointwise

.
open set
open_locale nat

lemma mediant_btwn {K : Type*} [linear_ordered_field K] {a b c d : K} (hc : 0 < c) (hd : 0 < d)
  (h : a / c < b / d) :
  a / c < (a + b) / (c + d) ∧
  (a + b) / (c + d) < b / d :=
begin
  rw div_lt_div_iff hc hd at h,
  rw [div_lt_div_iff (add_pos hc hd) hd, div_lt_div_iff hc (add_pos hc hd)],
  split;
  linarith,
end

/--
if b / d < a / c with ad - bc = 1
we have (a + b) / (c + d) in between
so (a + b) / (c + d) < a / c has same property ie
a * (c + d) - (a + b) * c = 1
and
b / d < (a + b) / (c + d) has same property ie
(a + b) * d - b * (c + d) = 1
-/
lemma mediant_unimod {a b c d : ℤ} (ha : a * d - b * c = 1) : a * (c + d) - (a + b) * c = 1 ∧
  (a + b) * d - b * (c + d) = 1 :=
begin
  ring_nf,
  rw mul_comm,
  simp [ha],
end

lemma mediant_reduced {a b c d : ℤ} (ha : a * d - b * c = 1) :
  (a + b).nat_abs.coprime (c + d).nat_abs :=
begin
  -- have := calc b + d = (b + d) * 1 : by simp
  --   ... = (b + d) * (a * d - b * c) : by rw ← ha
  --   ... = b * ((a + b) * d - b * (c + d)) + d * (a * (c + d) - (a + b) * c) : by ring,
  change (a + b).gcd (c + d) = 1,
  have := dvd_sub ((int.gcd_dvd_right (a + b) (c+d)).mul_left a)
                  ((int.gcd_dvd_left (a + b) (c+d)).mul_right c),
  rw (mediant_unimod ha).1 at this,
  rw ← int.nat_abs_dvd_iff_dvd at this,
  simpa using this,
end

-- See Apostol Modular forms and Dirichlet seties in number theory p. 98

lemma mediant_denom {a c : ℤ} {b d : ℕ} (hb : 0 < b) (ha : c * b - d * a = 1) : ((a + c : ℚ) / (b + d)).denom = b + d :=
begin
  -- TODO this is a horrible proof, serious cleanup needed
  rw mul_comm _ a at ha,
  rw add_comm b d,
  have := rat.denom_div_eq_of_coprime _ (mediant_reduced ha),
  rw add_comm c a at this,
  norm_cast at this,
  rw ← this,
  congr,
  simp only [add_comm, nat.cast_add],
  rw rat.mk_eq_div,
  norm_cast,
  norm_cast,
  linarith,
end

lemma farey_set_finite (n : ℕ) (x y : ℝ) :
  {r : ℝ | ∃ q : ℚ, (q.denom ≤ n ∧ x ≤ q ∧ ↑q ≤ y) ∧ ↑q = r}.finite :=
begin
  have nfact_pos : 0 < (n! : ℝ),
  { norm_cast,
    rw pos_iff_ne_zero,
    exact (nat.factorial_ne_zero n), },
  have : (((*) n! : ℝ → ℝ) '' _).finite,
  swap,
  apply this.of_finite_image,
  apply function.injective.inj_on,
  exact mul_right_injective₀ nfact_pos.ne.symm,
  { have : {t : ℝ | ∃ q : ℤ, (x * n! ≤ q ∧ ↑q ≤ y * n!) ∧ (↑q : ℝ) = t}.finite,
    { apply set.finite.image,
      change {r : ℤ | _}.finite,
      apply (finite_Icc ⌊x * ↑n!⌋ ⌈y * n!⌉).subset,
      rintros y ⟨hyl, hyr⟩,
      rw [mem_Icc],
      split,
      have := (int.floor_le _).trans hyl, -- TODO can this be a le_floor type iff lemma?
      exact_mod_cast this,
      have := hyr.trans (int.le_ceil _), -- TODO can this be a le_floor type iff lemma?
      exact_mod_cast this, },
    apply this.subset,
    intros x hx,
    rcases hx with ⟨hx_w, ⟨r, ⟨ha, hb, hc⟩, hd⟩, rfl⟩,
    simp only [←hd, mem_set_of_eq, eq_self_iff_true] at *,
    have key : (r * n!).denom = 1,
    { rw rat.mul_denom,
      simp only [rat.coe_nat_denom, mul_one, rat.coe_nat_num],
      suffices : (r.num * ↑n!).nat_abs.gcd r.denom = r.denom,
      simp only [this, nat.div_self r.pos],
      apply nat.gcd_eq_right,
      simp only [int.nat_abs_mul, int.nat_abs_of_nat],
      apply dvd_mul_of_dvd_right,
      apply nat.dvd_factorial r.pos ha, },
    use (r * n!).num,
    have := rat.coe_int_num_of_denom_eq_one key, -- TODO a general version of this for any coe
    apply_fun (coe : ℚ → ℝ) at this,
    push_cast at this,
    simp only [this],
    repeat { split },
    rwa mul_le_mul_right nfact_pos,
    rwa mul_le_mul_right nfact_pos,
    rw mul_comm, },
end
