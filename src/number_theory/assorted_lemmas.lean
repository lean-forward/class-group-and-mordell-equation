import ring_theory.noetherian
import ring_theory.polynomial.basic
import ring_theory.adjoin_root
import ring_theory.norm
import data.zmod.basic
import ring_theory.dedekind_domain.ideal
import linear_algebra.free_module.finite.basic
import ring_theory.class_group
import ring_theory.principal_ideal_domain
import tactic.slim_check
.

/-! This is essentially one big for_mathlib file
-/

/-! # Parity stuff-/
section parity

-- @[parity_simps]
lemma nat.coprime_two_iff_odd (n : ℕ) : n.coprime 2 ↔ ¬ even n :=
by rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd nat.prime_two,
    nat.two_dvd_ne_zero, nat.not_even_iff]
  -- simp only [nat.two_dvd_ne_zero, nat.not_even_iff] with parity_simps,
  -- TODO squeeze simp with doesn't remove the with?
-- @[parity_simps]
lemma nat.two_coprime_iff_odd (n : ℕ) : (2 : ℕ).coprime n ↔ ¬ even n :=
by rw [nat.coprime_comm, nat.coprime_two_iff_odd]

@[parity_simps]
lemma nat.coprime_bit0 (n m : ℕ) : n.coprime (bit0 m) ↔ ¬ even n ∧ n.coprime m :=
by rw [bit0_eq_two_mul, nat.coprime_mul_iff_right, nat.coprime_two_iff_odd]

@[parity_simps]
lemma nat.bit0_coprime (n m : ℕ) : (bit0 n).coprime m ↔ ¬ even m ∧ n.coprime m :=
by rw [nat.coprime_comm, nat.coprime_bit0, nat.coprime_comm]

example : ¬ (8 : ℕ).coprime 6 := by simp with parity_simps
example : (8 : ℕ).coprime 9 := by simp with parity_simps

end parity


/-! # zeroness of zmod powers-/
section pow_zmod_nat
variables {n m : ℕ} (e : ℕ)

-- TODO think if any generalized version of this with exponents in hyp would be useful

lemma pow_zmod_nat (h : (m : zmod n) = 0) : (m ^ e : zmod (n ^ e)) = 0 :=
begin
  norm_cast,
  rw zmod.nat_coe_zmod_eq_zero_iff_dvd at *,
  exact pow_dvd_pow_of_dvd h e,
end
end pow_zmod_nat
section pow_zmod_int
variables {n : ℕ} {m : ℤ} (e : ℕ)

lemma pow_zmod_int (h : (m : zmod n) = 0) : (m ^ e : zmod (n ^ e)) = 0 :=
begin
  norm_cast,
  rw zmod.int_coe_zmod_eq_zero_iff_dvd at *,
  push_cast,
  exact pow_dvd_pow_of_dvd h e,
end

end pow_zmod_int

section norm_zero
namespace algebra
lemma norm_zero_of_basis {R S ι : Type*} [comm_ring R] [comm_ring S] [algebra R S] [nontrivial S]
  [fintype ι] (b : basis ι R S) : algebra.norm R (0 : S) = 0 :=
begin
  have hι : nonempty ι := b.index_nonempty,
  letI := classical.dec_eq ι,
  rw algebra.norm_eq_matrix_det b,
  rw [alg_hom.map_zero, matrix.det_zero hι],
end

@[simp]
lemma norm_zero {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] [nontrivial R]
  [nontrivial S] [_root_.module.finite R S] [_root_.module.free R S] : algebra.norm R (0 : S) = 0 :=
norm_zero_of_basis (module.free.choose_basis R S)

end algebra
end norm_zero


section int_squarefree
lemma int.squarefree_iff_squarefree_nat_abs {z : ℤ} : squarefree z ↔ squarefree (int.nat_abs z) :=
begin
  rw [squarefree, squarefree],
  split; intros h x hx,
  { specialize h x _, norm_cast, rw ← int.coe_nat_dvd_left at hx, exact hx,
    norm_cast at h, exact h },
  { specialize h x.nat_abs _, rw ← int.nat_abs_mul, simpa, simp [nat.is_unit_iff] at h,
    exact int.is_unit_iff_nat_abs_eq.mpr h, }
end
-- namespace norm_num
-- open norm_num
-- open tactic
-- TODO try to get this working
-- @[norm_num] meta def eval_squarefree_int : expr → tactic (expr × expr)
-- | `(squarefree (%%e : ℤ)) := do
--   trace "hi mom",
--   return (`(squarefree (int.nat_abs (%%e : int))), `((@int.squarefree_iff_squarefree_nat_abs %%e).symm))
-- | _ := failed
-- end norm_num

end int_squarefree

section irred

lemma irreducible_of_map_irreducible {α β : Type*} [monoid α] [monoid β] [unique βˣ] {p : α}
  {F : Type*} [monoid_hom_class F α β] (f : F) (hf : ∀ x, f x = 1 → x = 1)
  (h : irreducible $ f p) : irreducible p :=
{ not_unit := λ hn, h.not_unit (hn.map f),
  is_unit_or_is_unit' := λ a b hab, begin
    have := map_mul f a b,
    rw ← hab at this,
    apply or.imp _ _ (h.is_unit_or_is_unit this);
    rintro ⟨ua, ha⟩;
    [rw hf a, rw hf b];
    { exact is_unit_one } <|>
    { simp [← ha], },
  end }

end irred

section zero_generator

open ideal
section noncomm
variables {R : Type*} [ring R]

-- TODO maybe submodule version

@[simp] lemma span_zero' : span ({0} : set R) = ⊥ := by simp
@[simp] lemma span_one : span ({1} : set R) = ⊤ := by simp
instance : submodule.is_principal (⊥ : ideal R) :=
{ principal := ⟨0, by {rw ← submodule.span_zero, refl}⟩ }
instance {a : R} : submodule.is_principal (span ({a} : set R)) := { principal := ⟨a, rfl⟩ }

@[simp]
lemma generator_bot : submodule.is_principal.generator (⊥ : ideal R) = 0 :=
begin
  apply mem_bot.mp,
  exact submodule.is_principal.generator_mem _,
end

lemma generator_zero : submodule.is_principal.generator (span ({0} : set R)) = 0 :=
by simp

open submodule.is_principal

lemma span_generator' (a : R) :
  ideal.span ({(generator (span ({a} : set R)))} : set R) = ideal.span {a} :=
ideal.span_singleton_generator _
end noncomm

section comm
variables {R : Type*} [comm_ring R]
open submodule.is_principal

local infix ` ~ᵤ ` : 50 := associated

-- TODO is the domain assumption needed?
lemma associated_generator_span_singleton [is_domain R] (a : R) :
  generator (span ({a} : set R)) ~ᵤ a := -- TODO notation for associated?
begin
  apply associated_of_dvd_dvd; rw ← mem_span_singleton,
  rw ideal.span_singleton_generator,
  exact submodule.mem_span_singleton_self _, -- maybe also an ideal version needed
  exact generator_mem _, -- TODO need ideal version for library search
end

-- TODO generalize these two
lemma norm_unit (u : Rˣ) : is_unit $ algebra.norm ℤ (u : R) :=
begin
  apply is_unit_of_mul_eq_one _ (algebra.norm ℤ (↑u⁻¹ : R)),
  simp [← _root_.map_mul],
end

-- TODO generalize these two
lemma norm_associated_of_associated {a b : R} (h : associated a b) :
  associated (algebra.norm ℤ a) (algebra.norm ℤ b) :=
begin
  obtain ⟨u, hu⟩ := h,
  apply_fun (algebra.norm ℤ) at hu,
  rw _root_.map_mul at hu,
  obtain ⟨Nu, hNu⟩ := norm_unit u,
  use Nu,
  rwa hNu,
end

end comm

end zero_generator

section top_generator

variables (R : Type*) [comm_ring R]
open submodule.is_principal

lemma is_unit_generator_top : is_unit (generator (⊤ : ideal R)) :=
is_unit_of_dvd_one (generator ⊤) $ (mem_iff_generator_dvd ⊤).mp submodule.mem_top

end top_generator
section class_group_span_singleton

@[simp]
lemma class_group.mk0_span_singleton {R K : Type*} [comm_ring R] [field K] [algebra R K]
  [is_fraction_ring R K] [is_domain R] [is_dedekind_domain R] (x : R) (h) :
  class_group.mk0 ⟨ideal.span ({x} : set R), h⟩ = 1 :=
begin
  rw class_group.mk0_eq_one_iff,
  exact ideal.span.submodule.is_principal,
end
end class_group_span_singleton

section mk0_pow
lemma units.mk0_pow {G₀ : Type*} [group_with_zero G₀] (x : G₀) {n : ℕ} (hn : 0 < n) (hxy) :
  units.mk0 (x ^ n) hxy = (units.mk0 x (λ h, hxy (by simp only [h, zero_pow_eq_zero, hn]))) ^ n :=
by { ext, simp, }
end mk0_pow

section poly_lemma
open_locale polynomial
open polynomial

-- TODO cleanup, maybe a general version for other powers less than multiplicity?
-- TODO probably delete as dup of mul_div_by_monic_eq_iff_is_root
lemma polynomial.div_by_monic_mul_eq {R : Type*} [comm_ring R] [is_domain R]
  (p : R[X]) (a : R) (ha : a ∈ p.roots) :
  p /ₘ (X - C a) * (X - C a) = p :=
have monic (X - C a), from (monic_X_sub_C _),
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2
    ((dvd_pow_self _ begin have := is_root_of_mem_roots ha,
        rw ← root_multiplicity_pos at this, exact this.ne.symm,
        intro hp, simpa [hp] using ha, end).trans (pow_root_multiplicity_dvd _ _))] };
  simp [mul_comm]

lemma polynomial.not_is_unit_of_nat_degree_pos {R : Type*} [comm_ring R] [is_domain R]
  (p : R[X]) (hpl : 0 < p.nat_degree) : ¬ is_unit p :=
begin
  intro h,
  have : p.nat_degree = 0,
  { simp [polynomial.nat_degree_eq_zero_iff_degree_le_zero,
      polynomial.degree_eq_zero_of_is_unit h], },
  simpa [this] using hpl,
end

lemma polynomial.irreducible_iff_roots_empty_of_degree_le_three {R : Type*} [field R]
  {p : R[X]} (hp : p.nat_degree ≤ 3) (hpl : 2 ≤ p.nat_degree) : irreducible p ↔ p.roots = 0 :=
begin
  have hpz : p ≠ 0 := polynomial.ne_zero_of_nat_degree_gt hpl,
  have hpu : ¬ is_unit p := p.not_is_unit_of_nat_degree_pos (pos_of_gt hpl),
  rw irreducible_iff,
  simp only [hpu, not_false_iff, true_and],
  split,
  { intro h,
    contrapose! h,
    obtain ⟨r, hr⟩ := multiset.exists_mem_of_ne_zero h,
    -- rw ← polynomial.div_by_monic_mul_pow_root_multiplicity_eq p r,
    refine ⟨p /ₘ (X - C r), X - C r, _, _, _⟩,
    { conv_lhs
      { rw [← mul_div_by_monic_eq_iff_is_root.mpr (is_root_of_mem_roots hr), mul_comm] }, },
    { apply polynomial.not_is_unit_of_nat_degree_pos,
      rw nat_degree_div_by_monic _ (monic_X_sub_C r), -- TODO why is there no degree version? is it false?
      simpa using hpl, },
    { apply polynomial.not_is_unit_of_nat_degree_pos,
      simp, }, },
  { rintro h a b rfl,
    simp only [not_or_distrib, ne.def, mul_eq_zero] at hpz,
    rw polynomial.nat_degree_mul hpz.1 hpz.2 at hp,
    -- sad wlog
    have key : ∀ (A B : R[X]) (Hpl : 2 ≤ (A * B).nat_degree) (Hpu : ¬is_unit (A * B))
      (H : (A * B).roots = 0) (Hpz : ¬A = 0 ∧ ¬B = 0) (Hp : A.nat_degree + B.nat_degree ≤ 3)
      (this : 1 ≤ A.nat_degree),
      is_unit A ∨ is_unit B,
    { clear_except,
      intros A B Hpl Hpu H Hpz Hp this,
      have : A.nat_degree ≤ 3 := le_of_add_le_left Hp,
      interval_cases A.nat_degree with H_eq,
      { exfalso,
        have : A.roots ≠ 0,
        { convert roots_ne_zero_of_splits (ring_hom.id _) (splits_of_nat_degree_eq_one _ H_eq)
            (by simp [H_eq]), -- TODO this probably should be simpler
          simp, },
        rw [roots_mul (mul_ne_zero Hpz.1 Hpz.2), add_eq_zero_iff] at H,
        exact this H.1, },
      { -- TODO deduplicate these somehow
        simp only [H_eq, is_unit.mul_iff, not_and, le_refl, nat.bit0_le_bit1_iff, eq_self_iff_true,
          nat.one_le_bit0_iff, nat.lt_one_iff] at *,
        rw ← le_tsub_iff_left (by norm_num : 2 ≤ 3) at Hp,
        norm_num at Hp,
        rw or_iff_not_imp_right,
        intro HB,
        exfalso,
        have : B.nat_degree = 1,
        { rw [is_unit_iff_degree_eq_zero, degree_eq_nat_degree Hpz.2, with_top.coe_eq_zero] at HB,
          interval_cases B.nat_degree with Hi,
          { simpa [Hi] using HB, },
          { simp [Hi], }, },
        have : B.roots ≠ 0,
        { convert roots_ne_zero_of_splits (ring_hom.id _) (splits_of_nat_degree_le_one _ Hp)
            (by simp [this]), -- TODO this probably should be simpler
          simp, },
        rw [roots_mul (mul_ne_zero Hpz.1 Hpz.2), add_eq_zero_iff] at H,
        exact this H.2, },
      { simp only [H_eq, ne.def, mul_eq_zero, is_unit.mul_iff, not_and, le_refl,
          nat.bit0_le_bit1_iff, eq_self_iff_true, add_le_iff_nonpos_right, le_zero_iff,
          polynomial.is_unit_iff_degree_eq_zero, not_or_distrib] at ⊢ Hp,
        right,
        rw [polynomial.degree_eq_nat_degree Hpz.2, Hp, enat.coe_zero], }, },
    have : 1 ≤ a.nat_degree ∨ 1 ≤ b.nat_degree, -- TODO this should be a lemma, with ceil (d / 2)
    { rw [nat_degree_mul hpz.1 hpz.2] at hpl,
      contrapose! hpl,
      linarith, },
    cases this,
    exact key a b hpl hpu h hpz hp this,
    exact (key b a (by simpa [mul_comm] using hpl) (by simpa [mul_comm] using hpu)
      (by simpa [mul_comm] using h) hpz.symm (by simpa [add_comm] using hp) this).symm, },
end

end poly_lemma


section unique_unit
@[simp] lemma is_unit_iff_eq_one {M : Type*} [monoid M] [hu : unique Mˣ] (m : M) :
  is_unit m ↔ m = 1 :=
begin
  split; intro h,
  { lift m to Mˣ using h,
    simp, },
  { simp [h], },
end
end unique_unit


section ring_equiv

@[simp] -- TODO which way is simp, also in the library?
lemma ring_equiv.to_equiv_symm {R S : Type*} [semiring R] [semiring S] (f : R ≃+* S) :
  (f : R ≃ S).symm = (f.symm : S ≃ R) := rfl

end ring_equiv


section dvd_sub_self

variables {α : Type*} [ring α]

theorem dvd_sub_iff_left {a b c : α} (h : a ∣ c) : a ∣ b ↔ a ∣ b - c :=
⟨λh₂, dvd_sub h₂ h, λH, by have t := dvd_add H h; rwa sub_add_cancel at t⟩

theorem dvd_sub_iff_right {a b c : α} (h : a ∣ b) : a ∣ c ↔ a ∣ b - c :=
⟨λh₂, dvd_sub h h₂, λH, by have t := dvd_sub h H; rwa [← sub_add, sub_self, zero_add] at t⟩

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_sub_left {a b c : α} (h : a ∣ c) : a ∣ b - c ↔ a ∣ b :=
(dvd_sub_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_sub_right {a b c : α} (h : a ∣ b) : a ∣ b - c ↔ a ∣ c :=
(dvd_sub_iff_right h).symm

/-- An element a divides the difference a - b if and only if a divides b.-/
@[simp] lemma dvd_sub_self_left {a b : α} : a ∣ a - b ↔ a ∣ b :=
dvd_sub_right (dvd_refl a)

/-- An element a divides the difference b - a if and only if a divides b.-/
@[simp] lemma dvd_sub_self_right {a b : α} : a ∣ b - a ↔ a ∣ b :=
dvd_sub_left (dvd_refl a)

end dvd_sub_self

section zmod_reduced

instance {n : ℕ} [fact $ squarefree n] : is_reduced (zmod n) :=
⟨begin
  casesI n,
  { exfalso,
    apply not_squarefree_zero _inst_1.out, },
  rintro ⟨x, hx⟩ ⟨_ | m, h⟩,
  { rw [pow_zero, fin.one_eq_zero_iff] at h,
    rw [h, nat.lt_one_iff] at hx,
    simp only [hx, fin.mk_zero], },
  { have : ((⟨x, hx⟩ : zmod n.succ) = (x : zmod n.succ)),
    { ext,
      simp only [fin.coe_mk, fin.coe_of_nat_eq_mod],
      exact (nat.mod_eq_of_lt hx).symm, },
    rw this at h ⊢,
    norm_cast at h,
    rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h ⊢,
    rwa unique_factorization_monoid.dvd_pow_iff_dvd_of_squarefree at h,
    exact fact.out _,
    exact ne_zero.ne _, }
end⟩

end zmod_reduced

section squarefree_gcd_of_squarefree

variables {α : Type*} [cancel_comm_monoid_with_zero α] [gcd_monoid α]

lemma squarefree_gcd_of_squarefree_right {a b : α} (hb : squarefree b) :
  squarefree (gcd a b) :=
λ x hx, hb x $ hx.trans $ gcd_dvd_right _ _

lemma squarefree_gcd_of_squarefree_left {a b : α} (ha : squarefree a) :
  squarefree (gcd a b) :=
λ x hx, ha x $ hx.trans $ gcd_dvd_left _ _

end squarefree_gcd_of_squarefree

@[simp]
lemma int.is_unit_coe_nat {n : ℕ} : is_unit (n : ℤ) ↔ n = 1 :=
by rw [int.is_unit_iff_nat_abs_eq, int.nat_abs_of_nat]

instance : Π (n : ℕ), slim_check.sampleable (zmod n)
| 0 := show slim_check.sampleable ℤ, by apply_instance
| (n+1) := show slim_check.sampleable (fin (n + 1)), by apply_instance


lemma is_square.nonneg {α : Type*} [linear_ordered_field α] {a : α} (h : is_square a) : 0 ≤ a :=
begin
  rcases h with ⟨h_w, rfl⟩,
  exact mul_self_nonneg h_w,
end
