import algebra.big_operators.norm_num
import data.nat.fib
import data.nat.succ_pred
import linear_algebra.basis
import ring_theory.adjoin_root
import ring_theory.power_basis
import tactic.norm_fin
import tactic.norm.ring

open_locale big_operators

local attribute [-instance] rat.semiring rat.comm_semiring rat.comm_ring

-- TODO: generalize this so we don't assume a multiplication on `S`
-- or even no structure on `S` at all
structure times_table (ι R S : Type*) [fintype ι]
  [semiring R] [add_comm_monoid S] [module R S] [has_mul S] :=
(basis : basis ι R S)
(table : ι → ι → ι → R)
(unfold_mul' : ∀ x y k, basis.repr (x * y) k = ∑ i j : ι, basis.repr x i * basis.repr y j * table i j k)
-- (mul_def : ∀ i j k, basis.repr (basis i * basis j) k = table i j k)

mk_simp_attribute times_table_simps "The simpset `times_table_simps` is used by the tactic
`times_table` to reduce an expression of the form `(t : times_table).basis.repr x k` to a numeral."

section add_monoid

variables {ι R S : Type*} [fintype ι] [semiring R] [add_comm_monoid S] [module R S] [has_mul S]

noncomputable def times_table.coord (t : times_table ι R S) (x : S) (i : ι) : R :=
t.basis.repr x i

@[simp] lemma times_table.basis_repr_eq (t : times_table ι R S) (x : S) (i : ι) :
  t.basis.repr x i = t.coord x i := rfl

@[simp] lemma times_table.coord_basis [decidable_eq ι] (t : times_table ι R S) (i : ι) :
  t.coord (t.basis i) = pi.single i 1 :=
by ext; rw [← t.basis_repr_eq, t.basis.repr_self i, finsupp.single_eq_pi_single]

lemma times_table.unfold_mul (t : times_table ι R S) :
  ∀ x y k, t.coord (x * y) k = ∑ i j : ι, t.coord x i * t.coord y j * t.table i j k :=
t.unfold_mul'

lemma times_table.ext (t : times_table ι R S) {x y : S} (h : ∀ i, t.coord x i = t.coord y i) :
  x = y :=
t.basis.ext_elem h

end add_monoid

section semiring
variables {ι R S : Type*} [fintype ι] [comm_semiring R] [non_unital_non_assoc_semiring S] [module R S]

@[simp] lemma times_table.mul_def (t : times_table ι R S) (i j k : ι)  :
  t.coord (t.basis i * t.basis j) k = t.table i j k :=
begin
  letI := classical.dec_eq ι,
  simp only [t.unfold_mul, times_table.coord_basis],
  rw [fintype.sum_eq_single i, fintype.sum_eq_single j, pi.single_eq_same,
      pi.single_eq_same, one_mul, one_mul];
    { intros x hx, simp [pi.single_eq_of_ne hx] }
end

variables [smul_comm_class R S S] [is_scalar_tower R S S]

@[simp] lemma linear_equiv.map_bit0 {R M N : Type*} [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (f : M ≃ₗ[R] N) (x : M) : f (bit0 x) = bit0 (f x) :=
by { unfold bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }
@[simp] lemma linear_equiv.map_bit1 {R M N : Type*} [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N] [has_one M]
  (f : M ≃ₗ[R] N) (x : M) : f (bit1 x) = bit0 (f x) + f 1 :=
by { unfold bit1 bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }

end semiring

namespace tactic.times_table

open tactic

section add_comm_monoid

variables {R S ι : Type*} [fintype ι] [comm_semiring R] [add_comm_monoid S] [module R S]
variables [has_mul S]

protected lemma coord_zero (t : times_table ι R S) (k : ι) :
  t.coord 0 k = 0 :=
by rw [← t.basis_repr_eq, _root_.map_zero, finsupp.zero_apply]

protected lemma coord_bit0 (t : times_table ι R S) (k : ι) {e₁ : S} {e₁' e' : R}
  (e₁_eq : t.coord e₁ k = e₁') (e_eq : e₁' + e₁' = e') :
  t.coord (bit0 e₁) k = e' :=
by rw [bit0, ← t.basis_repr_eq, _root_.map_add, finsupp.add_apply, t.basis_repr_eq, e₁_eq, e_eq]

protected lemma coord_bit1 [has_one S] (t : times_table ι R S) (k : ι) {e₁ : S} {e₁' e₁2 e' o : R}
  (e₁_eq : t.coord e₁ k = e₁') (one_eq : t.coord 1 k = o) (e2_eq : e₁' + e₁' = e₁2)
  (e_eq : e₁2 + o = e') :
  t.coord (bit1 e₁) k = e' :=
by simp only [← t.basis_repr_eq,bit1, bit0, _root_.map_add, finsupp.add_apply, t.basis_repr_eq,
  e₁_eq, e2_eq, one_eq, e_eq]

protected lemma coord_add (t : times_table ι R S) (k : ι) {e₁ e₂ : S} {e₁' e₂' e' : R}
  (e₁_eq : t.coord e₁ k = e₁') (e₂_eq : t.coord e₂ k = e₂') (e_eq : e₁' + e₂' = e') :
  t.coord (e₁ + e₂) k = e' :=
by rw [← t.basis_repr_eq,_root_.map_add, finsupp.add_apply, t.basis_repr_eq, e₁_eq, t.basis_repr_eq,
    e₂_eq, e_eq]

protected lemma coord_mul (t : times_table ι R S) (k : ι) (e₁ e₂ : S) (e' : R)
  (eq : ∑ i j : ι, t.coord e₁ i * t.coord e₂ j * t.table i j k = e') :
  t.coord (e₁ * e₂) k = e' :=
by rw [times_table.unfold_mul t, eq]

protected lemma coord_repr_table {ι : Sort*}
  {r₁i r₂j tijk e₁' e₂' t' e₁e₂ e' : R} (e₁_eq : r₁i = e₁') (e₂_eq : r₂j = e₂')
  (t_eq : tijk = t') (e₁e₂_eq : e₁' * e₂' = e₁e₂) (eq : e₁e₂ * t' = e') :
  r₁i * r₂j * tijk = e' :=
by rw [e₁_eq, e₂_eq, t_eq, e₁e₂_eq, eq]

end add_comm_monoid

section semiring

variables {R S ι : Type*} [fintype ι] [comm_semiring R] [semiring S] [module R S]

protected lemma eval_pow_zero (t : times_table ι R S) (k : ι) (e₁ : S) {e' : R}
  (e_eq : t.coord 1 k = e') :
  t.coord (e₁ ^ 0) k = e' :=
by rw [pow_zero, e_eq]

protected lemma eval_pow_one (t : times_table ι R S) (k : ι) {e₁ : S} {e' : R}
  (e_eq : t.coord e₁ k = e') :
  t.coord (e₁ ^ 1) k = e' :=
by rw [pow_one, e_eq]

protected lemma eval_pow_bit0 (t : times_table ι R S) (k : ι) (n : ℕ) {e₁ : S} {e' : R}
  (e_eq : t.coord (e₁ ^ n * e₁ ^ n) k = e') :
  t.coord (e₁ ^ (bit0 n)) k = e' :=
by rw [pow_bit0, e_eq]

protected lemma eval_pow_bit1 (t : times_table ι R S) (k : ι) (n : ℕ) {e₁ : S} {e' : R}
  (e_eq : t.coord (e₁ ^ n * e₁ ^ n * e₁) k = e') :
  t.coord (e₁ ^ (bit1 n)) k = e' :=
by rw [pow_bit1, e_eq]

end semiring

section ring

variables {R S ι : Type*} [fintype ι] [comm_ring R] [ring S] [module R S]

protected lemma coord_sub (t : times_table ι R S) (k : ι) {e₁ e₂ : S} {e₁' e₂' e' : R}
  (e₁_eq : t.coord e₁ k = e₁') (e₂_eq : t.coord e₂ k = e₂') (e_eq : e₁' - e₂' = e') :
  t.coord (e₁ - e₂) k = e' :=
by rw [← t.basis_repr_eq, _root_.map_sub, finsupp.sub_apply, t.basis_repr_eq, e₁_eq,
  t.basis_repr_eq, e₂_eq, e_eq]

protected lemma coord_neg (t : times_table ι R S) (k : ι) {e₁ : S} {e₁' e' : R}
  (e₁_eq : t.coord e₁ k = e₁') (e_eq : -e₁' = e') :
  t.coord (-e₁) k = e' :=
by rw [← t.basis_repr_eq, _root_.map_neg, finsupp.neg_apply, t.basis_repr_eq, e₁_eq, e_eq]

end ring

section matrix

open matrix

section converter

meta structure context :=
(simps : simp_lemmas)
(cache : tactic.norm.ring.cache)
(coord_univ : native.rb_map expr (expr × expr × list expr))

meta abbreviation eval_m (α : Type*) := state_t context tactic α

/-- Evaluates a parsed (in α) expression into a normal form (in β). -/
meta abbreviation evaluator (α β : Type*) := expr × α → eval_m (expr × expr × β)

meta abbreviation converter := expr → eval_m (expr × expr)

/-- `trace_error msg t` executes the tactic `t`. If `t` fails, traces `msg` and the failure message
of `t`. -/
meta def trace_error {α σ} (msg : string) (t : state_t σ tactic α) : state_t σ tactic α :=
{ run := λ s ts, match t.run s ts with
       | (result.success r s') := result.success r s'
       | (result.exception (some msg') p s') := (trace msg >> trace (msg' ()) >> result.exception
            (some msg') p) s'
       | (result.exception none p s') := result.exception none p s'
       end }

meta def lift {σ α} : tactic α → state_t σ tactic α := state_t.lift
meta def converter.lift {σ α β} : (α → tactic β) → α → state_t σ tactic β := λ t x, lift (t x)

meta def converter.refl : converter
| e := lift (refl_conv e)

meta def converter.or : converter → converter → converter
| c d e := c e <|> d e

meta def converter.or_refl (c : converter) : converter := c.or converter.refl

meta def converter.trans : converter → converter → converter
| c d e := do
  (e', pf_c) ← c.or_refl e,
  (e'', pf_d) ← d.or_refl e',
  pf ← lift $ mk_eq_trans pf_c pf_d,
  pure (e'', pf)

meta def get_context : state_t context tactic context :=
state_t.get

meta def to_expr' : pexpr → tactic expr := i_to_expr

meta def to_expr : pexpr → eval_m expr := lift ∘ to_expr'

end converter

namespace tactic.norm_num

/-- Use `norm_num` to decide equality between two expressions.
If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial: it will fail in cases where `norm_num` can't reduce either side
to a rational numeral.
-/
meta def decide_eq (l r : expr) : tactic (bool × expr) := do
  (l', l'_pf) ← or_refl_conv norm_num.derive l,
  (r', r'_pf) ← or_refl_conv norm_num.derive r,
  n₁ ← l'.to_rat, n₂ ← r'.to_rat,
  c ← infer_type l' >>= mk_instance_cache,
  if n₁ = n₂ then do
    pf ← mk_eq_symm r'_pf >>= mk_eq_trans l'_pf,
    pure (tt, pf)
  else do
    (_, p) ← norm_num.prove_ne c l' r' n₁ n₂,
    pure (ff, p)

lemma list.mem_cons_of_head {α : Type*} {x y : α} (ys : list α) (h₁ : x = y) :
  x ∈ y :: ys :=
(list.mem_cons_iff x y _).mpr (or.inl h₁)

lemma list.mem_cons_of_tail {α : Type*} {x y : α} {ys : list α} (h₂ : x ∈ ys) :
  x ∈ y :: ys :=
(list.mem_cons_iff x y _).mpr (or.inr h₂)

lemma list.not_mem_cons {α : Type*} {x y : α} {ys : list α} (h₁ : x ≠ y) (h₂ : x ∉ ys) :
  x ∉ y :: ys :=
λ h, ((list.mem_cons_iff _ _ _).mp h).elim h₁ h₂

/-- Use a decision procedure for the equality of list elements to decide list membership.
If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial iff its parameter `decide_eq` is partial.
-/
meta def list.decide_mem (decide_eq : expr → expr → tactic (bool × expr)) :
  expr → list expr → tactic (bool × expr)
| x [] := do
  pf ← mk_app `list.not_mem_nil [x],
  pure (ff, pf)
| x (y :: ys) := do
  (is_head, head_pf) ← decide_eq x y,
  if is_head then do
    pf ← mk_app `list.mem_cons_of_head [head_pf],
    pure (tt, pf)
  else do
    (mem_tail, tail_pf) ← list.decide_mem x ys,
    if mem_tail then do
      pf ← mk_app `list.mem_cons_of_tail [tail_pf],
      pure (tt, pf)
    else do
      pf ← mk_app `list.not_mem_cons [head_pf, tail_pf],
      pure (ff, pf)

lemma finset.insert_eq_coe_list_of_mem {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  {xs' : list α} (h : x ∈ xs') (nd_xs : xs'.nodup)
  (hxs' : xs = finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs)) :
  insert x xs = finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs) :=
have h : x ∈ xs, by simpa [hxs'] using h,
by rw [finset.insert_eq_of_mem h, hxs']

lemma finset.insert_eq_coe_list_cons {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  {xs' : list α} (h : x ∉ xs') (nd_xs : xs'.nodup) (nd_xxs : (x :: xs').nodup)
  (hxs' : xs = finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs)) :
  insert x xs = finset.mk ↑(x :: xs') (multiset.coe_nodup.mpr nd_xxs) :=
have h : x ∉ xs, by simpa [hxs'] using h,
by { rw [← finset.val_inj, finset.insert_val_of_not_mem h, hxs'], simp only [multiset.cons_coe] }

/-- Given an expression defeq to a natural numeral, return the value of this numeral.

This is a slightly more powerful version of `expr.to_nat`.
-/
meta def parse_nat : expr → option ℕ
| `(%%a + %%b) := do
  a' ← parse_nat a,
  b' ← parse_nat b,
  pure (a' + b')
| n := expr.to_nat n

lemma list.map_cons_congr {α β : Type*} (f : α → β) (x : α) (xs : list α) (fx : β) (fxs : list β)
  (h₁ : f x = fx) (h₂ : xs.map f = fxs) : (x :: xs).map f = fx :: fxs :=
by rw [list.map_cons, h₁, h₂]

meta def list.to_expr (α : expr) : list expr → tactic expr
| [] := mk_app `list.nil [α]
| (ex :: xs) := do
  exs ← list.to_expr xs,
  mk_app `list.cons [α, ex, exs]

/-- Apply `ef : α → β` to all elements of the list, constructing an equality proof.
`eval_f (x : expr) : tactic (expr × expr)` is a conversion procedure for simplifying expressions
of the form `(%%ef %%x), where `ef : expr` is the function to apply and `x : expr` is a list
element.
-/
meta def eval_list_map {α β : Type*} (ef : expr)
  (eval_f : expr × α → eval_m (expr × expr × β)) :
  expr → list (α) → state_t context tactic (list (expr × β) × expr)
| exs [] := do
  match exs with
  | `(list.nil) := do
    eq ← lift $ mk_app `list.map_nil [ef],
    pure ([], eq)
  | _ := lift $ fail!"eval_list_map: expecting `list.nil`, received {exs}"
  end
| `(list.cons %%ex %%exs) (x :: xs) := do
  (fx, fx_eq, fx_d) ← eval_f (ex, x),
  (fxs, fxs_eq) ← eval_list_map exs xs,
  ty ← lift $ infer_type fx,
  fxs_list ← lift $ list.to_expr ty (fxs.map prod.fst),
  eq ← lift $ mk_app `tactic.times_table.tactic.norm_num.list.map_cons_congr [ef, ex, exs, fx, fxs_list, fx_eq, fxs_eq],
  pure ((fx, fx_d) :: fxs, eq)
| exs (_ :: _) := lift $ fail format!"eval_list_map: expecting `list.cons _ _`, received {exs}"

lemma list.cons_congr {α : Type*} (x : α) {xs : list α} {xs' : list α} (xs_eq : xs' = xs) :
  x :: xs' = x :: xs :=
by rw xs_eq

lemma list.map_congr {α β : Type*} (f : α → β) {xs xs' : list α}
  {ys : list β} (xs_eq : xs = xs') (ys_eq : xs'.map f = ys) :
  xs.map f = ys :=
by rw [← ys_eq, xs_eq]

/-- Convert an expression denoting a list to a list of elements. -/
meta def eval_list : expr → eval_m (expr × expr × list expr)
| e@`(list.nil) := do
  eq ← lift $ mk_eq_refl e,
  pure (e, eq, [])
| e@`(list.cons %%x %%xs) := do
  (exs, xs_eq, xs) ← eval_list xs,
  e' ← lift $ mk_app `list.cons [x, exs],
  eq ← lift $ mk_app `list.cons_congr [x, xs_eq],
  pure (e', eq, x :: xs)
/-
| e@`(list.range %%en) := do
  n ← lift $ parse_nat en,
  eis ← lift $ (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← lift $ mk_eq_refl e,
  pure (eis, eq)
| `(@list.map %%α %%β %%ef %%exs) := do
  (xs, xs_eq) ← eval_list exs,
  (ys, ys_eq) ← eval_list_map ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  eq ← to_expr ``(list.map_congr %%ef %%xs_eq %%ys_eq),
  pure (ys, eq)
-/
| e@`(@list.fin_range %%en) := do
  n ← lift $ parse_nat en,
  eis ← (list.fin_range n).mmap (λ i, lift $ expr.of_nat `(fin %%en) i),
  eq ← lift $ mk_eq_refl e,
  let e'_list := eis.foldr (λ x xs, `(@list.cons (fin %%en) %%x %%xs)) `(@list.nil (fin %%en)),
  pure (e'_list, eq, eis)
| e := lift $ fail (to_fmt "Unknown list expression" ++ format.line ++ to_fmt e)

lemma multiset.cons_congr {α : Type*} (x : α) {xs : multiset α} {xs' : list α}
  (xs_eq : (xs' : multiset α) = xs) : (list.cons x xs' : multiset α) = x ::ₘ xs :=
by rw [← xs_eq]; refl

lemma multiset.map_congr {α β : Type*} (f : α → β) {xs : multiset α}
  {xs' : list α} {ys : list β} (xs_eq : xs = (xs' : multiset α)) (ys_eq : xs'.map f = ys) :
  xs.map f = (ys : multiset β) :=
by rw [← ys_eq, ← multiset.coe_map, xs_eq]

/-- Convert an expression denoting a multiset to a list of elements,
normalizing the expression to a sequence of `multiset.cons` and `0`.
We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).
-/
meta def eval_multiset : expr → eval_m (expr × expr × list expr)
| e@`(@has_zero.zero (multiset _) _) := do
  eq ← lift $ mk_eq_refl e,
  pure (e, eq, [])
| e@`(@has_emptyc.emptyc _ %%inst) := do
  eq ← lift $ mk_eq_refl e,
  pure (e, eq, [])
| e@`(has_singleton.singleton %%x) := do
  eq ← lift $ mk_eq_refl e,
  pure (e, eq, [x])
| e@`(multiset.cons %%x %%xs) := do
  (exs, xs_eq, xs) ← eval_multiset xs,
  e' ← lift $ mk_app `multiset.cons [x, exs],
  eq ← lift $ mk_app `multiset.cons_congr [x, xs_eq],
  pure (e', eq, x :: xs)
| e@`(@@has_insert.insert multiset.has_insert %%x %%xs) := do
  (exs, xs_eq, xs) ← eval_multiset xs,
  e' ← lift $ mk_app `multiset.cons [x, exs],
  eq ← lift $ mk_app `multiset.cons_congr [x, xs_eq],
  pure (e', eq, x :: xs)
/-
| e@`(multiset.range %%en) := do
  n ← lift $ parse_nat en,
  eis ← lift $ (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← lift $ mk_eq_refl e,
  pure (eis, eq)
| `(@multiset.map %%α %%β %%ef %%exs) := do
  (xs, xs_eq) ← eval_multiset exs,
  (ys, ys_eq) ← eval_list_map ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  eq ← to_expr ``(multiset.map_congr %%ef %%xs_eq %%ys_eq),
  pure (ys, eq)
-/
| `(@@coe (@@coe_to_lift (@@coe_base (multiset.has_coe))) %%exs) := do
  (exs, xs_eq, xs) ← trace_error "eval_list" $ eval_list exs,
  e ← to_expr ``(@@coe (@@coe_to_lift (@@coe_base (multiset.has_coe))) %%exs),
  eq ← to_expr ``(congr_arg coe %%xs_eq),
  pure (e, eq, xs)
| e := lift $ fail (to_fmt "Unknown multiset expression" ++ format.line ++ to_fmt e)

lemma finset.mk_congr {α : Type*} {xs xs' : multiset α} (h : xs = xs') (nd nd') :
  finset.mk xs nd = finset.mk xs' nd' :=
by congr; assumption

lemma finset.nodup_congr {α : Type*} (xs xs' : multiset α) (h : xs = xs') (nd : xs.nodup) :
  xs'.nodup :=
by rwa h at nd

/-- Convert an expression denoting a finset to an expression of the form `finset.mk ↑xs nodup`.
We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).
`decide_eq` is a (partial) decision procedure for determining whether two
elements of the finset are equal, for example to parse `{2, 1, 2}` into `[2, 1]`.
-/
meta def eval_finset (decide_eq : expr → expr → tactic (bool × expr)) :
  expr → eval_m (expr × expr × list expr)
| e@`(finset.mk %%val %%nd) := do
  (norm, eq, val') ← trace_error "eval_multiset" $ eval_multiset val,
  nd' ← to_expr ``(finset.nodup_congr %%val %%norm %%eq %%nd),
  e' ← to_expr ``(finset.mk %%norm %%nd'),
  eq' ← to_expr ``(finset.mk_congr %%eq %%nd %%nd'),
  pure (e', eq', val')
/-
| e@`(has_emptyc.emptyc) := do
  eq ← mk_eq_refl e,
  nd ← to_expr' ``(list.nodup_nil),
  pure ([], eq, nd)
| e@`(has_singleton.singleton %%x) := do
  eq ← mk_eq_refl e,
  nd ← to_expr' ``(list.nodup_singleton %%x),
  pure ([x], eq, nd)
| `(@@has_insert.insert (@@finset.has_insert %%dec) %%x %%xs) := do
  (exs, xs_eq, xs_nd) ← eval_finset xs,
  (is_mem, mem_pf) ← list.decide_mem decide_eq x exs,
  if is_mem then do
    pf ← to_expr' ``(finset.insert_eq_coe_list_of_mem %%x %%xs %%mem_pf %%xs_nd %%xs_eq),
    pure (exs, pf, xs_nd)
  else do
    nd ← to_expr' ``(list.nodup_cons.mpr ⟨%%mem_pf, %%xs_nd⟩),
    pf ← to_expr' ``(finset.insert_eq_coe_list_cons %%x %%xs %%mem_pf %%xs_nd %%nd %%xs_eq),
    pure (x :: exs, pf, nd)
-/
| `(@@finset.univ %%ft) := trace_error "eval_finset `finset.univ`" $ do
  -- Convert the fintype instance expression `ft` to a list of its elements.
  -- Unfold it to the `fintype.mk` constructor and a list of arguments.
  `fintype.mk ← lift $ get_app_fn_const_whnf ft
    | lift $ fail (to_fmt "Unknown fintype expression" ++ format.line ++ to_fmt ft),
  [_, args, _] ← lift $ get_app_args_whnf ft | lift $ fail (to_fmt "Expected 3 arguments to `fintype.mk`"),
  msg ← lift $ pformat!"error in recursive call `eval_finset {args}`",
  trace_error msg.to_string $ eval_finset args
| e@`(finset.range %%en) := do
  n ← lift $ parse_nat en,
  eis ← lift $ (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← lift $ mk_eq_refl e,
  let e'_list := eis.foldr (λ x xs, `(@list.cons ℕ %%x %%xs)) `(@list.nil ℕ),
  e' ← to_expr ``(finset.mk ↑%%e'_list (multiset.coe_nodup.mpr (list.nodup_range %%en))),
  pure (e', eq, eis)
| e := lift $ fail (to_fmt "Unknown finset expression" ++ format.line ++ to_fmt e)

@[to_additive]
lemma list.prod_cons_congr {α : Type*} [monoid α] (xs : list α) (x y z : α)
  (his : xs.prod = y) (hi : x * y = z) : (x :: xs).prod = z :=
by rw [list.prod_cons, his, hi]

/-
/-- Evaluate `list.prod %%xs`,
producing the evaluated expression and an equality proof. -/
meta def list.prove_prod (α : expr) : list expr → tactic (expr × expr)
| [] := do
  result ← expr.of_nat α 1,
  proof ← to_expr' ``(@list.prod_nil %%α _),
  pure (result, proof)
| (x :: xs) := do
  eval_xs ← list.prove_prod xs,
  xxs ← to_expr' ``(%%x * %%eval_xs.1),
  eval_xxs ← or_refl_conv norm_num.derive xxs,
  exs ← expr.of_list α xs,
  proof ← to_expr'
    ``(list.prod_cons_congr %%exs%%x %%eval_xs.1 %%eval_xxs.1 %%eval_xs.2 %%eval_xxs.2),
  pure (eval_xxs.1, proof)
-/

/-- Evaluate `list.sum %%xs`,
producing the evaluated expression and an equality proof. -/
meta def list.prove_sum {α : Type*}
  (eval_zero : eval_m (expr × expr × α)) (eval_add : expr × α → expr × α → eval_m (expr × expr × α))
  (M : expr) : list (expr × α) → eval_m (expr × expr × α)
| [] := do
  ⟨zero, _, zero_d⟩ ← eval_zero,
  proof ← to_expr ``(@list.sum_nil %%M _),
  pure ⟨zero, proof, zero_d⟩
| (x :: xs) := do
  ⟨sxs, sxs_pf, sxs_d⟩ ← list.prove_sum xs,
  ⟨sxxs, sxxs_pf, sxxs_d⟩ ← eval_add x (sxs, sxs_d),
  exs ← lift $ expr.of_list M (xs.map prod.fst),
  proof ← to_expr
    ``(list.sum_cons_congr %%exs %%x.1 %%sxs %%sxxs %%sxs_pf %%sxxs_pf),
  pure ⟨sxxs, proof, sxxs_d⟩

@[to_additive] lemma list.prod_congr {α : Type*} [monoid α] {xs xs' : list α} {z : α}
  (h₁ : xs = xs') (h₂ : xs'.prod = z) : xs.prod = z := by cc

@[to_additive] lemma multiset.prod_congr {α : Type*} [comm_monoid α]
  {xs : multiset α} {xs' : list α} {z : α}
  (h₁ : xs = (xs' : multiset α)) (h₂ : xs'.prod = z) : xs.prod = z :=
by rw [← h₂, ← multiset.coe_prod, h₁]

/-
/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).prod`,
producing the evaluated expression and an equality proof.
`eval_f : expr → tactic (expr × expr)` is a conversion procedure for simplifying expressions
of the form `(%%ef %%x), where `ef : expr` is the function to apply and `x : expr` is a list
element.
-/
meta def list.prove_prod_map (β ef : expr) (eval_f : converter)
  (xs : list expr) : state_t context tactic (expr × expr) := do
  (fxs, fxs_eq) ← eval_list_map ef eval_f xs,
  (prod, prod_eq) ← lift $ list.prove_prod β fxs,
  eq ← to_expr ``(list.prod_congr %%fxs_eq %%prod_eq),
  pure (prod, eq)
-/

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).sum`,
producing the evaluated expression and an equality proof.
`eval_f : expr → tactic (expr × expr)` is a conversion procedure for simplifying expressions
of the form `(%%ef %%x), where `ef : expr` is the function to apply and `x : expr` is a list
element.
-/
meta def list.prove_sum_map (M ef : expr)
  {α β : Type*}
  (eval_zero : eval_m (expr × expr × α)) (eval_add : expr × α → expr × α → eval_m (expr × expr × α))
  (eval_f : expr × β → eval_m (expr × expr × α))
  (exs : expr) (xs : list β) : eval_m (expr × expr × α) :=
trace_error "internal error in prove_sum_map" $ do
  (fxs, fxs_eq) ← eval_list_map ef eval_f exs xs,
  (sum, sum_eq, sum_d) ← list.prove_sum eval_zero eval_add M fxs,
  eq ← to_expr ``(list.sum_congr %%fxs_eq %%sum_eq),
  pure (sum, eq, sum_d)

@[to_additive]
lemma finset.eval_prod_of_list {β α : Type*} [comm_monoid β]
  (s : finset α) (f : α → β) {is : list α} (his : is.nodup)
  (hs : finset.mk ↑is (multiset.coe_nodup.mpr his) = s)
  {x : β} (hx : (is.map f).prod = x) :
  s.prod f = x :=
by rw [← hs, finset.prod_mk, multiset.coe_map, multiset.coe_prod, hx]

meta def eval_finset_sum {α β : Type*} (eval_set : expr × unit → eval_m (expr × expr × list β))
  (eval_zero : eval_m (expr × expr × α)) (eval_add : expr × α → expr × α → eval_m (expr × expr × α))
  (eval_f : expr → expr × β → eval_m (expr × expr × α)) (eβ ef : expr) (es : expr) :
  eval_m (expr × expr × α) :=
trace_error "internal error in eval_finset_sum" $ do
  (es', list_eq, xs) ← eval_set (es, ()),
  match es' with
  | `(finset.mk (coe %%exs) %%nodup) := do
    (result, sum_eq, result_d) ← list.prove_sum_map eβ ef eval_zero eval_add (eval_f ef) exs xs,
    pf ← to_expr ``(finset.eval_sum_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
    pure (result, pf, result_d)
  | _ := do
    lift $ fail format!"eval_finset_sum: expected `finset.mk _ _`, received {es'}"
  end

/-- `eval_set` takes a `finset` expression and returns a tuple consisting of:
 * the normal form, of the form `finset.mk (↑bs) nodup`, where `is` is a sequence of `list.cons` and `list.nil`
 * the normalization proof
 * a list of extra information, one per term in `bs` -/
meta def norm_finset_sum {α β : Type*} (eval_set : expr × unit → eval_m (expr × expr × list β))
  (eval_zero : eval_m (expr × expr × α)) (eval_add : expr × α → expr × α → eval_m (expr × expr × α))
  (eval_f : expr → expr × β → eval_m (expr × expr × α)) : expr → eval_m (expr × expr × α)
| `(@finset.sum %%β %%α %%inst %%es %%ef) := eval_finset_sum eval_set eval_zero eval_add eval_f β ef es
| e := lift $ fail $ format! "norm_finset_sum: expected ∑ i in s, f i, got {e}"

/-
/-- `norm_num` plugin for evaluating big operators:
 * `list.prod`
 * `list.sum`
 * `multiset.prod`
 * `multiset.sum`
 * `finset.prod`
 * `finset.sum`
-/
meta def eval_big_operators : converter
| `(@list.prod %%α %%inst1 %%inst2 %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_list exs,
  (result, sum_eq) ← lift $ list.prove_prod α xs,
  pf ← to_expr ``(list.prod_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@list.sum %%α %%inst1 %%inst2 %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_list exs,
  (result, sum_eq) ← list.prove_sum (converter.or_refl $ converter.lift norm_num.derive) α xs,
  pf ← to_expr ``(list.sum_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@multiset.prod %%α %%inst %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_multiset exs,
  (result, sum_eq) ← lift $ list.prove_prod α xs,
  pf ← to_expr ``(multiset.prod_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@multiset.sum %%α %%inst %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_multiset exs,
  (result, sum_eq) ← list.prove_sum (converter.or_refl $ converter.lift norm_num.derive) α xs,
  pf ← to_expr ``(multiset.sum_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@finset.prod %%β %%α %%inst %%es %%ef) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq, nodup) ← lift $ eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_prod_map β ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  pf ← to_expr ``(finset.eval_prod_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| `(@finset.sum %%β %%α %%inst %%es %%ef) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq, nodup) ← lift $ eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_sum_map β ef (converter.or_refl $ converter.lift norm_num.derive) (converter.or_refl $ converter.lift norm_num.derive) xs,
  pf ← to_expr ``(finset.eval_sum_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| _ := lift $ failed
-/

end tactic.norm_num

lemma eval_vec_cons_pf_zero {α : Type*} {n : ℕ} (x : α) (xs : fin n → α) :
  vec_cons x xs has_zero.zero = x := rfl
lemma eval_vec_cons_pf_succ {α : Type*} {n : ℕ} (i : fin n) (x y : α) (xs : fin n → α)
  (h : xs i = y) : vec_cons x xs (fin.succ i) = y :=
by rw [cons_val_succ, h]

/-- `eval_vec_cons n x xs` returns `(y, ⊢ vec_cons x xs n = y)` -/
meta def eval_vec_cons : ℕ → expr → expr → tactic (expr × expr)
| 0 x xs := do
  eq ← mk_app ``eval_vec_cons_pf_zero [x, xs],
  pure (x, eq)
| (n + 1) x' xxs@`(vec_cons %%x %%xs) := do
  (result, eq') ← eval_vec_cons n x xs,
  eq ← to_expr' ``(eval_vec_cons_pf_succ _ %%x' %%result %%xxs %%eq'),
  pure (result, eq)
| (n + 1) x xs := tactic.trace xs >> fail "Expected vector of the form `vec_cons x y`"

open tactic.norm_fin

@[norm_num]
meta def norm_vec_cons : expr → tactic (expr × expr)
| `(vec_cons %%x %%xs %%i) := i.to_nat >>= λ n, tactic.trace_error "Internal error in `norm_vec_cons`." $ do
  (y, pf) ← tactic.trace_error "" $ eval_vec_cons n x xs,
  pure (y, pf)
| e := pformat!"norm_vec_cons: expected `vec_cons x xs i`, got {e}" >>= fail

end matrix

/-- Simplify expressions of the form `(t : times_table).coord x k` using lemmas tagged
`@[times_table_simps]`. -/
-- @[norm_num]
meta def simp_times_table : converter
| e := do
  ctx ← get_context,
  (e', pf, _) ← state_t.lift $ simplify ctx.simps [] e <|>
    fail!"Failed to simplify {e}, are you missing a `@[times_table_simps]` lemma?",
  pure (e', pf)

protected lemma eval_vec_cons_pf {α ι : Type*} (t : ι → ι → ι → α) (i j k : ι)
  {ti : ι → ι → α} (ti_pf : t i = ti) {tij : ι → α} (tij_pf : ti j = tij) :
  t i j k = tij k :=
by rw [ti_pf, tij_pf]

meta def head_beta' (e : expr) : state_t context tactic expr :=
trace_error "error in head_beta" $ lift (head_beta e)

meta def conv_pexpr (conv : converter) (e : pexpr) : state_t context tactic (expr × expr) :=
lift (to_expr' e) >>= conv

meta def norm_cf : expr → state_t context tactic (expr × expr × ℚ)
| e := do
  (e', pf) ← converter.or_refl (converter.lift norm_num.derive) e,
  match e'.to_rat with
  | (some p) := pure (e', pf, p)
  | _ := failure
  end

meta def eval_add_cf : (expr × ℚ) → (expr × ℚ) → state_t context tactic (expr × expr × ℚ)
| (e₁, n₁) (e₂, n₂) := do
  (e', pf) ← conv_pexpr (converter.or_refl $ converter.lift norm_num.derive) ``(%%e₁ + %%e₂),
  pure (e', pf, n₁ + n₂)

meta def eval_neg_cf : (expr × ℚ) → state_t context tactic (expr × expr × ℚ)
| (e, n) := do
  (e', pf) ← conv_pexpr (converter.or_refl $ converter.lift norm_num.derive) ``(- %%e),
  pure (e', pf, -n)

meta def eval_mul_cf : (expr × ℚ) → (expr × ℚ) → state_t context tactic (expr × expr × ℚ)
| (e₁, n₁) (e₂, n₂) := do
  (e', pf) ← conv_pexpr (converter.or_refl $ converter.lift norm_num.derive) ``(%%e₁ * %%e₂),
  pure (e', pf, n₁ * n₂)

meta def eval_pow_cf : (expr × ℚ) → (expr × ℕ) → state_t context tactic (expr × expr × ℚ)
| (e₁, n₁) (e₂, n₂) := do
  (e', pf) ← conv_pexpr (converter.or_refl $ converter.lift norm_num.derive) ``(%%e₁ ^ %%e₂),
  pure (e', pf, n₁ ^ n₂)

meta instance : tactic.norm.ring.monad_ring (state_t context tactic) :=
⟨λ _, lift,
 λ _, failure,
 context.cache <$> state_t.get⟩

meta def eval_ring : evaluator unit (tactic.norm.ring.horner_expr ℚ)
| e := do
  (horner, pf) ← tactic.norm.ring.eval norm_cf eval_add_cf eval_neg_cf eval_mul_cf eval_pow_cf e.1,
  pure (horner.e, pf, horner)

meta def eval_ring_zero (M : expr) : eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ) :=
do
  zero ← lift $ expr.of_nat M 0,
  pf ← lift $ mk_eq_refl zero,
  pure (zero, pf, tactic.norm.ring.horner_expr.const zero 0)

meta def eval_ring_one (M : expr) : eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ) :=
do
  one ← lift $ expr.of_nat M 1,
  pf ← lift $ mk_eq_refl one,
  pure (one, pf, tactic.norm.ring.horner_expr.const one 1)

meta def eval_ring_add (l r : expr × tactic.norm.ring.horner_expr ℚ) :
  eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ) := do
do
  (e', p') ← tactic.norm.ring.eval_add eval_add_cf l.2 r.2,
  return (e', p', e')

meta def eval_ring_mul (l r : expr × tactic.norm.ring.horner_expr ℚ) :
  eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ) := do
do
  (e', p') ← tactic.norm.ring.eval_mul eval_add_cf eval_mul_cf l.2 r.2,
  return (e', p', e')

lemma unfold_sub {α} [add_group α] (a b b' c : α)
  (hb : -b = b') (h : a + b' = c) : a - b = c :=
by rw [sub_eq_add_neg, hb, h]

meta def eval_ring_sub (l r : expr × tactic.norm.ring.horner_expr ℚ) :
  eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ) := do
do
  (r', r'_eq) ← tactic.norm.ring.eval_neg eval_neg_cf r.2,
  (e', p') ← tactic.norm.ring.eval_add eval_add_cf l.2 r',
  p ← to_expr ``(unfold_sub %%(l.2 : expr) %%(r.2 : expr) %%(r' : expr) %%(e' : expr) %%r'_eq %%p'),
  return (e', p, e')

meta def eval_ring_neg (e : expr × tactic.norm.ring.horner_expr ℚ) :
  eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ) := do
do
  (e', p') ← tactic.norm.ring.eval_neg eval_neg_cf e.2,
  return (e', p', e')

meta def mk_cached_finset_univ (ι inst : expr) (ctx : context) : eval_m (expr × expr × list expr) :=
do
  `fintype.mk ← lift $ get_app_fn_const_whnf inst
    | lift $ fail (format!"Unknown fintype expression {inst}"),
  [_, args, _] ← lift $ get_app_args_whnf inst | lift $ fail (format!"Expected 3 arguments to `fintype.mk`"),
  result ← trace_error "eval_finset" $ tactic.norm_num.eval_finset tactic.norm_num.decide_eq args,
  state_t.put { coord_univ := ctx.coord_univ.insert ι result, .. ctx },
  pure result

meta def get_cached_finset_univ : expr × unit → eval_m (expr × expr × list expr)
| (`(@finset.univ %%ι %%inst), _) :=
  do ctx ← get_context,
    match ctx.coord_univ.find ι with
    | (some cu) := pure cu
    | none := mk_cached_finset_univ ι inst ctx
    end
| e := lift $ fail format!"get_cached_finset_univ: expected `(univ : finset _)`, got {e}"

meta def eq_rhs (e : expr) : tactic expr := do
  t ← infer_type e,
  match t with
  | `(_ = %%rhs) := pure rhs
  | _ := fail!"eq_rhs: expecting type of form `(_ = _), got {t}"
  end

/-- Evaluate expressions of the form `t.coord e₁ i * t.coord e₂ j * t.table i j k`.

`eval_coord` is a procedure for evaluating expression of the form `t.coord %%e %%i`.
This is passed as a separate parameter since Lean's support for mutual recursion is limited,
and we tie the recursive knot ourselves.
-/
meta def eval_mul_mul (ι R : expr)
  (eval_coord : expr → expr → eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ)) :
  expr → eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ)
| `(%%e₁i * %%e₂j * %%tableij) := trace_error "internal error in `eval_mul_mul`" $ do
  ι_sort ← lift $ infer_type ι,
  ι_level ← match ι_sort.match_sort with
  | (some ι_level) := pure ι_level
  | none := lift $ fail!"expecting (ι : Type), got ({ι} : {ι_sort})"
  end,

  -- Simplify and evaluate `t.coord e₁ i`
  (e₁i', e₁i_pf₁) ← simp_times_table.trans (converter.lift norm_vec_cons) e₁i,
  (e₁i', e₁i_pf₂, e₁i_expr) ← match e₁i' with
  | `(times_table.coord %%t %%e₁ %%i) := eval_coord e₁ i
  | _ := eval_ring (e₁i', ())
  end,
  e₁i_pf ← lift $ mk_eq_trans e₁i_pf₁ e₁i_pf₂,

  -- Simplify and evaluate `t.coord e₂ j`
  (e₂j', e₂j_pf₁) ← simp_times_table.trans (converter.lift norm_vec_cons) e₂j,
  (e₂j', e₂j_pf₂, e₂j_expr) ← match e₂j' with
  | `(times_table.coord %%t %%e₁ %%i) := eval_coord e₁ i
  | _ := eval_ring (e₂j', ())
  end,
  e₂j_pf ← lift $ mk_eq_trans e₂j_pf₁ e₂j_pf₂,

  -- Simplify and evaluate `t.table i j k`
  (tableij', tableij_pf₁) ← simp_times_table.trans (λ e, match e with
  | (expr.app (expr.app ti@(expr.app t i) j) k) := do
    (ti', ti_pf) ← lift $ norm_vec_cons ti,
    (tij', tij_pf) ← lift $ norm_vec_cons (expr.app ti' j),
    pf ← lift $ mk_app `tactic.times_table.eval_vec_cons_pf [R, ι, t, i, j, k, ti', ti_pf, tij', tij_pf],
    pure (expr.app tij' k, pf)
  | e := lift $ pformat!"expected `t.table i j k`, got {e}" >>= fail
  end) tableij,
  (tableij', tableij_pf₂, tableij_expr) ← eval_ring (tableij', ()),
  tableij_pf ← lift $ mk_eq_trans tableij_pf₁ tableij_pf₂,

  (e₁e₂, e₁e₂_pf, e₁e₂_expr) ← eval_ring_mul (e₁i', e₁i_expr) (e₂j', e₂j_expr),
  (e', e_pf, he') ← eval_ring_mul (e₁e₂, e₁e₂_expr) (tableij', tableij_expr),
  pf ← norm.ring.ic_lift (λ ic, do
    let n := `tactic.times_table.coord_repr_table,
    let l := [ι, e₁i, e₂j, tableij, e₁i', e₂j', tableij', e₁e₂, e', e₁i_pf, e₂j_pf, tableij_pf,
              e₁e₂_pf, e_pf],
    d ← get_decl n,
    (ic, l) ← ic.append_typeclasses d.type.binding_body l,
    return (ic, (expr.const n [ic.univ, ι_level]).mk_app (ic.α :: l))  ),
  pure (e', pf, he')
| e := lift $ pformat!"expected `t.coord e₁ i * t.coord e₂ j * t.table i j k`, got {e}" >>= fail

/-- Normalize `((t : times_table _ _ _).coord e) k` into Horner form. -/
protected meta def eval (ι R S t : expr) :
  expr → expr → eval_m (expr × expr × tactic.norm.ring.horner_expr ℚ)
| `(0) k := trace_error "zero" $ do
  e ← lift $ expr.of_nat R 0,
  pf ← to_expr ``(tactic.times_table.coord_zero %%t %%k),
  pure (e, pf, tactic.norm.ring.horner_expr.const e 0)
| `(bit0 %%e₁) k := trace_error "bit0" $ do
  (e₁', e₁_eq, he₁') ← eval e₁ k,
  (e', e_eq, he') ← eval_ring_add (e₁', he₁') (e₁', he₁'),
  eq ← to_expr ``(tactic.times_table.coord_bit0 %%t %%k %%e₁_eq %%e_eq),
  pure (e', eq, he')
| `(bit1 %%e₁) k := trace_error "bit1" $ do
  (e₁', e₁_eq, he₁') ← eval e₁ k,
  (one', one_eq, hone') ← (lift $ expr.of_nat S 1) >>= (λ e, eval e k),
  (e', e_eq, he') ← eval_ring_add (e₁', he₁') (e₁', he₁'),
  (e'', e'_eq, he'') ← eval_ring_add (e', he') (one', hone'),
  eq ← to_expr ``(tactic.times_table.coord_bit1 %%t %%k %%e₁_eq %%one_eq %%e_eq %%e'_eq),
  pure (e'', eq, he'')
| `(%%e₁ + %%e₂) k := trace_error "add" $ do
  (e₁', e₁_eq, he₁') ← eval e₁ k,
  (e₂', e₂_eq, he₂') ← eval e₂ k,
  (e', e_eq, he') ← eval_ring_add (e₁', he₁') (e₂', he₂'),
  eq ← to_expr ``(tactic.times_table.coord_add %%t %%k %%e₁_eq %%e₂_eq %%e_eq),
  pure (e', eq, he')
| `(%%e₁ - %%e₂) k := trace_error "sub" $ do
  (e₁', e₁_eq, he₁') ← eval e₁ k,
  (e₂', e₂_eq, he₂') ← eval e₂ k,
  (e', e_eq, he') ← eval_ring_sub (e₁', he₁') (e₂', he₂'),
  eq ← to_expr ``(tactic.times_table.coord_sub %%t %%k %%e₁_eq %%e₂_eq %%e_eq),
  pure (e', eq, he')
| `(-%%e₁) k := trace_error "neg" $ do
  (e₁', e₁_eq, he₁') ← eval e₁ k,
  (e', e_eq, he') ← eval_ring_neg (e₁', he₁'),
  eq ← to_expr ``(tactic.times_table.coord_neg %%t %%k %%e₁_eq %%e_eq),
  pure (e', eq, he')
| e@`(%%e₁ * %%e₂) k := trace_error "error in mul" $ do
  eq_sum_mul_times_table ← lift $ mk_app `times_table.unfold_mul [t, e₁, e₂, k],
  e ← lift $ eq_rhs eq_sum_mul_times_table,
  (e', e_eq, he') ← tactic.norm_num.norm_finset_sum get_cached_finset_univ (eval_ring_zero R) eval_ring_add -- evaluates the sum over i
    (λ f ⟨i, ei⟩, do
      term ← lift $ whnf (f i) transparency.reducible,
      tactic.norm_num.norm_finset_sum get_cached_finset_univ (eval_ring_zero R) eval_ring_add -- evaluates the sum over j
        (λ f ⟨j, _⟩, do
          term ← lift $ whnf (f j) transparency.reducible,
          eval_mul_mul ι R eval term)
        term)
    e,
  eq ← lift $ mk_eq_trans eq_sum_mul_times_table e_eq,
  pure (e', eq, he')
| `(%%e₁ ^ %%n) k := trace_error "pow" $ do
  match norm_num.match_numeral n with
  | norm_num.match_numeral_result.zero := do
    one ← lift $ expr.of_nat S 1,
    (one', one_eq, hone') ← eval one k,
    eq ← to_expr ``(tactic.times_table.eval_pow_zero %%t %%k %%e₁ %%one_eq),
    pure (one', eq, hone')
  | norm_num.match_numeral_result.one := do
    (e', e₁_eq, he') ← eval e₁ k,
    eq ← to_expr ``(tactic.times_table.eval_pow_one %%t %%k %%e₁_eq),
    pure (e', eq, he')
  | norm_num.match_numeral_result.bit0 b := do
    e₁' ← to_expr ``((%%e₁ ^ %%b) * (%%e₁ ^ %%b)),
    (e', e_eq, he') ← eval e₁' k,
    eq ← to_expr ``(tactic.times_table.eval_pow_bit0 %%t %%k %%b %%e_eq),
    pure (e', eq, he')
  | norm_num.match_numeral_result.bit1 b := do
    e₁' ← to_expr ``((%%e₁ ^ %%b) * (%%e₁ ^ %%b) * %%e₁),
    (e', e_eq, he') ← eval e₁' k,
    eq ← to_expr ``(tactic.times_table.eval_pow_bit1 %%t %%k %%b %%e_eq),
    pure (e', eq, he')

  | _ := lift $ tactic.fail "Expecting numeral in exponent"
  end
| e k := trace_error "times_table_simps" $ do
  full_e ← to_expr ``(times_table.coord %%t %%e %%k),
  (e', pr) ← simp_times_table full_e,
  (e'', pr', he'') ← eval_ring (e', ()),
  pf ← lift $ mk_eq_trans pr pr',
  pure (e'', pf, he'')

/--
`run_converter' atoms ek conv e` returns a `conv`-normalized form of `ek` = `f e`,
where `f` is some arbitrary function.

See also `run_converter` if you're running on only one subexpression.
-/
meta def run_converter' (atoms : ref (buffer expr)) (ek : expr) : converter → expr → tactic (expr × expr)
| conv e := do
  (simps, _) ← mk_simp_set tt [`times_table_simps]
    [simp_arg_type.expr ``(mul_zero), simp_arg_type.expr ``(zero_mul), simp_arg_type.expr ``(mul_one), simp_arg_type.expr ``(one_mul),
     simp_arg_type.expr ``(add_zero), simp_arg_type.expr ``(zero_add)],
  α ← infer_type ek,
  u ← mk_meta_univ,
  infer_type α >>= unify (expr.sort (level.succ u)),
  u ← get_univ_assignment u,
  ic ← mk_instance_cache α,
  (ic, c) ← ic.get ``comm_semiring,
  nc ← mk_instance_cache `(ℕ),
  using_new_ref ic $ λ r,
  using_new_ref nc $ λ nr,
    let cache : norm.ring.cache := ⟨α, u, c, transparency.semireducible, r, nr, atoms⟩ in do
    (result, _) ← (conv e).run { simps := simps, cache := cache, coord_univ := native.rb_map.mk _ _ },
    pure result

/--
`run_converter ek conv e` returns a `conv`-normalized form of `ek` = `f e`, where `f` is some arbitrary function.
-/
meta def run_converter (ek : expr) : converter → expr → tactic (expr × expr)
| conv e := using_new_ref mk_buffer $ λ atoms, run_converter' atoms ek conv e

set_option eqn_compiler.max_steps 4096

/-- Normalize expressions of the form `t.coord _`. -/
protected meta def norm_conv : converter
| ek@(expr.app (expr.app `(times_table.coord %%t) e) k) := do
  ι ← lift $ infer_type k,
  S ← lift $ infer_type e,
  R ← lift $ infer_type ek,
  (e', pf, he') ← trace_error "Internal error in `tactic.times_table.eval`:" $
    tactic.times_table.eval ι R S t e k,
  pf_ty ← lift $ infer_type pf,
  match pf_ty with
  | `(%%lhs = %%rhs) := do
    lift $ is_def_eq ek lhs <|> (trace "lhs does not match:" >> trace ek >> trace " ≠ " >> trace lhs),
    lift $ is_def_eq e' rhs <|> (trace "rhs does not match:" >> trace e' >> trace " ≠ " >> trace rhs)
  | _ := lift $ trace "Proof type is not an equality: " >> trace pf_ty
  end,
  pure (e', pf)
| _ := failure

/-- `norm_num` extension for expressions of the form `times_table.coord t _` -/
@[norm_num]
protected meta def norm : expr → tactic (expr × expr)
| ek@(expr.app (expr.app `(times_table.coord %%t) e) k) := do
  ι ← infer_type k,
  S ← infer_type e,
  R ← infer_type ek,
  (e', pf) ← tactic.trace_error "Internal error in `tactic.times_table.eval`:" $
    run_converter ek (λ e, tactic.times_table.eval ι R S t e k >>= λ eph, pure (eph.1, eph.2.1)) e,
  pf_ty ← infer_type pf,
  match pf_ty with
  | `(%%lhs = %%rhs) := do
    is_def_eq ek lhs <|> (trace "lhs does not match:" >> trace ek >> trace " ≠ " >> trace lhs),
    is_def_eq e' rhs <|> (trace "rhs does not match:" >> trace e' >> trace " ≠ " >> trace rhs)
  | _ := trace "Proof type is not an equality: " >> trace pf_ty
  end,
  pure (e', pf)
| _ := failure

meta def conv_subexpressions (step : expr → tactic (expr × expr)) (e : expr) : tactic (expr × expr) :=
do e ← instantiate_mvars e,
   (_, e', pr) ←
    ext_simplify_core () {} simp_lemmas.mk (λ _, trace "no discharger" >> failed) (λ _ _ _ _ _, failed)
      (λ _ _ _ _ e,
        do (new_e, pr) ← step e,
           guard (¬ new_e =ₐ e) <|> (trace "rewriting was idempotent: " >> trace e >> trace " → " >> trace new_e >> failure),
           return ((), new_e, some pr, tt))
      `eq e,
    return (e', pr)

end tactic.times_table

namespace tactic.interactive

open tactic

setup_tactic_parser

/-- Tactic for proving equalities of polynomial expressions in a finite extension of a base ring. -/
meta def times_table (red : parse (tk "!")?) : tactic unit :=
let transp := if red.is_some then semireducible else reducible in
do `(%%e₁ = %%e₂) ← target >>= instantiate_mvars,
  using_new_ref mk_buffer $ λ atoms, do
    (e₁', p₁) ← (tactic.times_table.run_converter' atoms e₁ tactic.times_table.norm_conv) e₁,
    (e₂', p₂) ← (tactic.times_table.run_converter' atoms e₂ tactic.times_table.norm_conv) e₂,
    is_def_eq e₁' e₂',
    p ← mk_eq_symm p₂ >>= mk_eq_trans p₁,
    tactic.exact p

end tactic.interactive
