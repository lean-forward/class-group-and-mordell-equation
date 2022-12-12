import tactic.times_table
import number_theory.quad_ring.basic

open polynomial

open_locale big_operators

-- TODO: could generalize to infinite ι
noncomputable def has_mul_of_table {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R) :
    has_mul S :=
{ mul := λ x y, b.equiv_fun.symm (λ k, ∑ i j, b.repr x i * b.repr y j * table i j k) }

lemma mul_def' {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R)
  (x y : S) (k : ι) :
  b.repr (by { letI := has_mul_of_table b table; exact x * y }) k = ∑ i j, b.repr x i * b.repr y j * table i j k :=
show b.repr (b.equiv_fun.symm (λ k, ∑ i j, b.repr x i * b.repr y j * table i j k)) k =
  ∑ i j, b.repr x i * b.repr y j * table i j k,
by simp only [← b.equiv_fun_apply, b.equiv_fun.apply_symm_apply]

lemma mul_def {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R)
  (i j k : ι) :
  b.repr (by { letI := has_mul_of_table b table; exact b i * b j }) k = table i j k :=
begin
  letI := classical.dec_eq ι,
  rw [mul_def', fintype.sum_eq_single i, fintype.sum_eq_single j],
  { simp },
  { intros k hk, simp [finsupp.single_eq_of_ne hk.symm] },
  { intros k hk, simp [finsupp.single_eq_of_ne hk.symm] },
end

-- TODO: could generalize to infinite ι
-- See note [reducible non-instances]
@[reducible]
noncomputable def non_unital_non_assoc_semiring_of_table {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R) :
    non_unital_non_assoc_semiring S :=
{ zero := 0,
  add := (+),
  mul := λ x y, b.equiv_fun.symm (λ k, ∑ i j, b.repr x i * b.repr y j * table i j k),
  zero_mul := λ x, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_zero, finsupp.zero_apply, zero_mul, finset.sum_const_zero] }),
  mul_zero := λ x, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_zero, finsupp.zero_apply, mul_zero, zero_mul, finset.sum_const_zero] }),
  left_distrib := λ x y z, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_add, finsupp.add_apply, mul_add, add_mul, finset.sum_add_distrib, ← b.equiv_fun_apply, b.equiv_fun.apply_symm_apply] }),
  right_distrib := λ x y z, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_add, finsupp.add_apply, mul_add, add_mul, finset.sum_add_distrib, ← b.equiv_fun_apply, b.equiv_fun.apply_symm_apply] }),
  .. hS }

namespace sqrt_d

variables (d : ℚ)

def table : fin 2 → fin 2 → fin 2 → ℚ :=
![![![1, 0], ![0, 1]],
  ![![0, 1], ![d, 0]]]

/-- Alternative definition of `quad_ring ℚ 0 d` -/
def sqrt_d (d : ℚ) := fin 2 → ℚ

section

local attribute [semireducible] sqrt_d

variables {d}

def mk (a b : ℚ) : sqrt_d d := ![a, b]

variables (d)

def sqrt : sqrt_d d := ![0, 1]

instance : add_comm_group (sqrt_d d) := pi.add_comm_group

noncomputable instance : non_unital_non_assoc_semiring (sqrt_d d) :=
non_unital_non_assoc_semiring_of_table (pi.basis_fun ℚ (fin 2)) (table d)

instance : module ℚ (sqrt_d d) := pi.module _ _ _

noncomputable abbreviation basis : basis (fin 2) ℚ (sqrt_d d) := pi.basis_fun ℚ (fin 2)

instance : smul_comm_class ℚ (sqrt_d d) (sqrt_d d) :=
⟨λ m n a, (basis d).ext_elem (λ k, by {
  rw [smul_eq_mul, smul_eq_mul, linear_equiv.map_smul, finsupp.smul_apply, mul_def', mul_def'],
  simp,
  ring })⟩

instance : is_scalar_tower ℚ (sqrt_d d) (sqrt_d d) :=
⟨λ m n a, (basis d).ext_elem (λ k, by {
  rw [smul_eq_mul, smul_eq_mul, linear_equiv.map_smul, finsupp.smul_apply, mul_def', mul_def'],
  simp,
  ring })⟩

noncomputable def times_table : times_table (fin 2) ℚ (sqrt_d d) :=
{ basis := by convert pi.basis_fun ℚ (fin 2),
  table := table d,
  unfold_mul' := sorry }

end

@[times_table_simps] lemma table_apply (i j k : fin 2) :
  (sqrt_d.times_table d).table i j k =
  ![![![1, 0], ![0, 1]],
    ![![0, 1], ![d, 0]]] i j k := rfl

@[times_table_simps] lemma coord_mk (a b : ℚ) (i : fin 2) :
  (sqrt_d.times_table d).coord (mk a b) i = ![a, b] i :=
rfl

variables {d}

@[elab_as_eliminator]
lemma cases (x : sqrt_d d) {p : sqrt_d d → Prop} (h : p (mk (x 0) (x 1))) :
  p x :=
sorry

set_option profiler true

-- 600ms
lemma mul_comm' (x y : quad_ring ℚ 0 d) : x * y = y * x :=
by quad_ring.calc_tac

-- 1s
lemma mul_comm (x y : sqrt_d d) : x * y = y * x :=
begin
  refine cases x _, refine cases y _,
  apply (sqrt_d.times_table d).ext (λ k, _),
  fin_cases k; times_table,
end

-- 1.3s
lemma mul_assoc' (x y z : quad_ring ℚ 0 d) : x * y * z = x * (y * z) :=
by quad_ring.calc_tac

-- 2.5s
lemma mul_assoc (x y z : sqrt_d d) : x * y * z = x * (y * z) :=
begin
  refine cases x _, refine cases y _, refine cases z _,
  apply (sqrt_d.times_table d).ext (λ k, _),
  fin_cases k; times_table,
end

instance : has_one (sqrt_d d) := ⟨![1, 0]⟩

@[times_table_simps] lemma coord_one : (sqrt_d.times_table d).coord 1 = ![1, 0] := rfl

noncomputable instance : comm_semiring (sqrt_d d) :=
{ one := 1,
  mul_assoc := mul_assoc,
  mul_comm := mul_comm,
  one_mul := λ x, cases x ((sqrt_d.times_table d).ext (λ k, by fin_cases k; times_table)),
  mul_one := λ x, cases x ((sqrt_d.times_table d).ext (λ k, by fin_cases k; times_table)),
  .. sqrt_d.non_unital_non_assoc_semiring d }

noncomputable instance : comm_ring (sqrt_d d) :=
{ .. sqrt_d.add_comm_group d, .. sqrt_d.comm_semiring }

section
set_option profiler true

-- calc_tac with a bit of help: 18s
lemma quad_ring.pow_three_sub_pow_three (x y : quad_ring ℚ 0 d) :
  x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) :=
by { refine quad_ring.ext _ _ _ _; simp [pow_succ]; ring_nf }

-- times_table: 28s
lemma times_table.pow_three_sub_pow_three (x y : sqrt_d d) :
  x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) :=
begin
  refine cases x _, refine cases y _,
  apply (sqrt_d.times_table d).ext (λ k, _),
  fin_cases k; times_table
end

-- calc_tac with a bit of help: 62.9s
lemma quad_ring.pow_four_sub_pow_four (x y : quad_ring ℚ 0 d) :
  x^4 - y^4 = (x - y) * (x^3 + x^2 * y + x * y^2 + y^3) :=
by { refine quad_ring.ext _ _ _ _; simp [pow_succ]; ring_nf }

-- times_table: 108s
lemma times_table.pow_four_sub_pow_four (x y : sqrt_d d) :
  x^4 - y^4 = (x - y) * (x^3 + x^2 * y + x * y^2 + y^3) :=
begin
  refine cases x _, refine cases y _,
  apply (sqrt_d.times_table d).ext (λ k, _),
  fin_cases k; times_table
end

end


end sqrt_d

#exit

-- Define a new structure
-- Might just as well have been a synonym for `adjoin_root (X^2 - 3 : (adjoin_root (X^2 - 2))[X]),
-- but this shows off the general design.
@[ext]
structure sqrt_2_sqrt_3 :=
(a b c d : ℚ)

namespace sqrt_2_sqrt_3

instance : add_comm_group sqrt_2_sqrt_3 :=
{ zero := ⟨0, 0, 0, 0⟩,
  add := λ x y, ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩,
  add_comm := λ x y, by { ext : 1; apply add_comm },
  add_zero := λ x, by { ext : 1; apply add_zero },
  zero_add := λ x, by { ext : 1; apply zero_add },
  add_assoc := λ x y z, by { ext : 1; apply add_assoc },
  neg := λ x, ⟨-x.a, -x.b, -x.c, -x.d⟩,
  add_left_neg := λ x, by { ext : 1; apply add_left_neg },
  sub := λ x y, ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩ }

.

instance : module ℚ sqrt_2_sqrt_3 :=
{ smul := λ c x, ⟨c * x.a, c * x.b, c * x.c, c * x.d⟩,
  add_smul := λ c d x, by { ext : 1; apply add_mul },
  smul_add := λ c x y, by { ext : 1; apply mul_add },
  mul_smul := λ c d x, by { ext : 1; apply mul_assoc },
  one_smul := λ x, by { ext : 1; apply one_mul },
  smul_zero := λ c, by { ext : 1; apply mul_zero },
  zero_smul := λ x, by { ext : 1; apply zero_mul } }

noncomputable def basis : basis (fin 4) ℚ sqrt_2_sqrt_3 :=
basis.of_equiv_fun $
{ to_fun := λ x, ![x.a, x.b, x.c, x.d],
  inv_fun := λ x, ⟨x 0, x 1, x 2, x 3⟩,
  left_inv := λ ⟨a, b, c, d⟩, rfl,
  right_inv := λ x, by { ext i : 1, fin_cases i; simp },
  map_add' := λ ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩, by { ext i : 1, fin_cases i; refl },
  map_smul' := λ r ⟨a, b, c, d⟩, by { ext i : 1, fin_cases i; refl } }

def table : fin 4 → fin 4 → fin 4 → ℚ :=
![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
  ![![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]],
  ![![0, 0, 1, 0], ![0, 0, 0, 1], ![3, 0, 0, 0], ![0, 3, 0, 0]],
  ![![0, 0, 0, 1], ![0, 0, 2, 0], ![0, 3, 0, 0], ![6, 0, 0, 0]]]

noncomputable def mul : sqrt_2_sqrt_3 →ₗ[ℚ] sqrt_2_sqrt_3 →ₗ[ℚ] sqrt_2_sqrt_3 :=
sqrt_2_sqrt_3.basis.constr ℚ $ λ i,
sqrt_2_sqrt_3.basis.constr ℚ $ λ j,
sqrt_2_sqrt_3.basis.equiv_fun.symm (table i j)

noncomputable instance : has_mul sqrt_2_sqrt_3 :=
{ mul := λ x y, mul x y }

instance : has_one sqrt_2_sqrt_3 :=
⟨⟨1, 0, 0, 0⟩⟩

@[simp] lemma sqrt_2_sqrt_3.basis_repr (x : sqrt_2_sqrt_3) :
  ⇑(sqrt_2_sqrt_3.basis.repr x) = ![x.a, x.b, x.c, x.d] :=
rfl

noncomputable def sqrt_2_sqrt_3.times_table : times_table (fin 4) ℚ sqrt_2_sqrt_3 :=
{ basis := sqrt_2_sqrt_3.basis,
  table := sqrt_2_sqrt_3.table,
  unfold_mul' := sorry }

@[simp, times_table_simps] -- TODO: get rid of `@[simp]`
lemma sqrt_2_sqrt_3.times_table_apply (i j k : fin 4) :
  sqrt_2_sqrt_3.times_table.table i j k =
  ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
    ![![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]],
    ![![0, 0, 1, 0], ![0, 0, 0, 1], ![3, 0, 0, 0], ![0, 3, 0, 0]],
    ![![0, 0, 0, 1], ![0, 0, 2, 0], ![0, 3, 0, 0], ![6, 0, 0, 0]]] i j k :=
rfl

@[times_table_simps] lemma coord_one (i : fin 4) :
  sqrt_2_sqrt_3.times_table.coord 1 i = ![1, 0, 0, 0] i := rfl


@[simp, times_table_simps] lemma coord_mk (a b c d : ℚ) (i : fin 4) :
  sqrt_2_sqrt_3.times_table.coord ⟨a, b, c, d⟩ i = ![a, b, c, d] i := rfl

def sqrt_2 : sqrt_2_sqrt_3 := ⟨0, 1, 0, 0⟩
@[times_table_simps] lemma coord_sqrt_2 (i : fin 4) :
  sqrt_2_sqrt_3.times_table.coord sqrt_2 i = ![0, 1, 0, 0] i := rfl

def sqrt_3 : sqrt_2_sqrt_3 := ⟨0, 0, 1, 0⟩
@[times_table_simps] lemma coord_sqrt_3 (i : fin 4) :
  sqrt_2_sqrt_3.times_table.coord sqrt_3 i = ![0, 0, 1, 0] i := rfl

@[simp]
lemma finsupp.bit0_apply {α M : Type*} [add_monoid M] (f : α →₀ M) (i : α) : (bit0 f) i = bit0 (f i) := rfl

end sqrt_2_sqrt_3
namespace sqrt_2_sqrt_3

-- set_option trace.type_context.is_def_eq_detail true
-- set_option trace.class_instances true

protected lemma mul_comm (x y : sqrt_2_sqrt_3) : x * y = y * x :=
begin
  cases x, cases y,
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table
end

protected lemma mul_assoc (x y z : sqrt_2_sqrt_3) : x * y * z = x * (y * z) :=
begin
  cases x, cases y, cases z,
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table
end

protected lemma left_distrib (x y z : sqrt_2_sqrt_3) : x * (y + z) = x * y + x * z :=
begin
  cases x, cases y, cases z,
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table
end

protected lemma right_distrib (x y z : sqrt_2_sqrt_3) : (x + y) * z = x * z + y * z :=
begin
  cases x, cases y, cases z,
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table
end

noncomputable instance : comm_ring sqrt_2_sqrt_3 :=
{ add := (+),
  zero := 0,
  mul := (*),
  one := 1,
  neg := has_neg.neg,
  one_mul := λ x, by { cases x, apply sqrt_2_sqrt_3.times_table.ext (λ k, _), fin_cases k; times_table },
  mul_one := λ x, by { cases x, apply sqrt_2_sqrt_3.times_table.ext (λ k, _), fin_cases k; times_table },
  left_distrib := sqrt_2_sqrt_3.left_distrib,
  right_distrib := sqrt_2_sqrt_3.right_distrib,
  mul_comm := sqrt_2_sqrt_3.mul_comm,
  mul_assoc := sqrt_2_sqrt_3.mul_assoc,
  .. sqrt_2_sqrt_3.add_comm_group }

-- Here's a concrete example of an equation that `times_table_tac` can solve
lemma eq₁ : (sqrt_2 + sqrt_3)^3 - 9 * (sqrt_2 + sqrt_3) = 2 * sqrt_2 :=
begin
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table,
end

lemma eq₂ (x y : sqrt_2_sqrt_3) : (x - y) * (x^2 + x * y + y^2) = x^3 - y^3 :=
begin
  cases x, cases y,
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table
end

@[times_table_simps] lemma coord_coe_int {a : ℤ} (k : fin 4) :
  sqrt_2_sqrt_3.times_table.coord ↑a k = ![a, 0, 0, 0] k :=
sorry

example (a b : sqrt_2_sqrt_3) : a + -b = a - b :=
begin
  cases a, cases b,
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table,
end

-- More equations to solve
example (a b : ℤ) : (a + b * sqrt_2 : sqrt_2_sqrt_3) * (a - b * sqrt_2) = a^2 - 2 * b^2 :=
begin
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table,
end

-- More equations to solve
example (a b c d : ℤ) :
  (a + b * sqrt_2 + c * sqrt_3 + d * sqrt_2 * sqrt_3 : sqrt_2_sqrt_3) *
  (a - b * sqrt_2 + c * sqrt_3 - d * sqrt_2 * sqrt_3 : sqrt_2_sqrt_3) *
  (a + b * sqrt_2 - c * sqrt_3 - d * sqrt_2 * sqrt_3 : sqrt_2_sqrt_3) *
  (a - b * sqrt_2 - c * sqrt_3 + d * sqrt_2 * sqrt_3 : sqrt_2_sqrt_3) =
  a^4 - 4*a^2*b^2 + 4*b^4 - 6*a^2*c^2 - 12*b^2*c^2 + 9*c^4 + 48 * a * b * c  *d - 12*a^2*d^2 -
    24*b^2*d^2 - 36*c^2*d^2 + 36*d^4 :=
begin
  apply sqrt_2_sqrt_3.times_table.ext (λ k, _),
  fin_cases k; times_table,
end

end sqrt_2_sqrt_3
