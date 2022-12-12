import tactic
import data.polynomial.basic
import data.polynomial.degree.definitions
import data.polynomial.eval
import data.list.func
import data.nat.prime
import data.matrix.notation
import linear_algebra.matrix.determinant
import tactic.sageify.socket
.

class has_sageify (R : Type*) :=
(sageify : R → string)
class has_sageify_type (R : Type*) :=
(sageify_type : string)

namespace has_sageify
open has_sageify_type
instance : has_sageify ℕ := ⟨λ n, to_string n⟩
instance : has_sageify ℤ := ⟨λ n, to_string n⟩
instance : has_sageify ℚ := ⟨λ n, to_string n⟩

instance : has_sageify_type ℤ := ⟨"Integers()"⟩
instance : has_sageify_type ℚ := ⟨"Rationals()"⟩
-- instance : has_sageify_type ℝ := ⟨λ n, "RDF()"⟩
-- instance : has_sageify_type ℂ := ⟨λ n, "CDF()"⟩

instance {R S : Type*} [has_sageify R] [has_sageify S] : has_sageify (R × S) :=
⟨λ n, "(" ++ sageify n.1 ++ ", " ++ sageify n.2 ++ ")"⟩
instance {R : Type*} [has_sageify R] : has_sageify (list R) :=
⟨λ n, "[" ++ ", ".intercalate (n.map (sageify)) ++ "]"⟩

instance {R : Type*} [semiring R] [has_sageify R] [has_sageify_type R] :
  has_sageify (polynomial R) :=
⟨λ n,
  let coeffs : list R := (list.range (n.nat_degree + 1)).map n.coeff in
  sformat!"PolynomialRing({sageify_type R})({sageify coeffs})"⟩
end has_sageify

class has_from_sage (R : Type*) :=
(sage_parser : parser R)

namespace parser


-- unlike the mathlib  one we allow "2" as a rat, and not only "2/1"
def possible_rat : parser ℚ := decorate_error "<rationals>" $ do
  ing ← int,
  di ← many (ch '/'),
  if 0 < di.length then do
    na ← nat,
    pure $ (ing : ℚ) / na
  else
    pure ing

def list {R : Type*} (pR : parser R) : parser (list R) := decorate_error "<list>" $ do
  ch '[',
  l ← many (do
    l ← pR,
    str ", ",
    pure l),
  ch ']',
  pure l
#eval (list (nat)).run_string "[1]"

end parser

namespace has_from_sage

-- dangerous!
def from_sage {R : Type*} [has_from_sage R] (s : string) : option R :=
(sage_parser.run_string s).get_right
def ifrom_sage {R : Type*} [has_from_sage R] [inhabited R] (s : string) : R :=
(from_sage s).iget
-- TODO fix this to remove all space
def strip_from_sage {R : Type*} [has_from_sage R] [inhabited R] (s : string) : option R :=
let s := if s.head = ' ' then s.popn 1 else s in
let s := if s.back = ' ' then s.popn_back 1 else s in
from_sage s

instance : has_from_sage ℕ := ⟨parser.nat⟩
instance : has_from_sage ℤ := ⟨parser.int⟩
instance : has_from_sage ℚ := ⟨parser.possible_rat⟩
#eval (ifrom_sage "-1232/113" : ℚ)

instance {R : Type*} [has_from_sage R] : has_from_sage (list R) :=
-- ⟨λ n, ((n.popn 1).pop_back.split (= ',')).map strip_from_sage⟩
⟨do
  parser.ch '[',
  h ← parser.sep_by (parser.str ", ") sage_parser,
  parser.ch ']',
  pure h⟩
#eval (ifrom_sage "[-1232/113, 12]" : list ℚ)
#eval (ifrom_sage "[12113, 12]" : list ℚ)

instance {R S : Type*} [has_from_sage R] [has_from_sage S] : has_from_sage (R × S) :=
⟨do
  parser.ch '(',
  l ← (sage_parser : parser R),
  parser.str ", ",
  r ← (sage_parser : parser S),
  parser.ch ')',
  pure (l, r)⟩
-- ⟨λ n, let st := ((n.popn 1).pop_back.split (= ',')) in
--   (strip_from_sage st.head, strip_from_sage st.tail.head)⟩

#eval (ifrom_sage "[(-1232/113, 1), (12, 1)]" : list (ℚ × ℕ))
instance {R : Type*} [has_from_sage R] [semiring R] : has_from_sage (polynomial R) :=
sorry
-- ⟨λ n, (parser.rat.run_string n).get_right.get_or_else 0⟩

#eval (ifrom_sage "[([-1, 1], 1), ([1], 1)]" : list (list ℚ × ℕ))

end has_from_sage

def sage_config : io.process.spawn_args :=
{ cmd := "conda",
  args := ["run", "-n", "sage", "sage", "-q"],
  stdin := io.process.stdio.piped,
  stderr := io.process.stdio.piped,
  stdout := io.process.stdio.piped
  }

def sage_io_config : io.process.spawn_args :=
{ cmd := "conda",
  args := ["run", "-n", "sage", "--no-capture-output", "sage", "-q"],
      --     -- "--simple-prompt" -- unclear if helpful
  stdin := io.process.stdio.piped,
  stderr := io.process.stdio.piped,
  stdout := io.process.stdio.piped
  }

def sage_io_config' : io.process.spawn_args :=
{ cmd := "sage",
  args := ["-q"],
  stdin := io.process.stdio.piped,
  stderr := io.process.stdio.piped,
  stdout := io.process.stdio.piped
  }

-- no longer needed
def escape (s : string) : string := "\\\"".intercalate $ s.split (= '\"')

open list.func
#check rat.reflect
run_cmd do to_string <$> tactic.eval_expr ℕ `(2 + 2) >>= tactic.trace

-- meta def reify_poly_aux (R : Type*) [has_add R] [has_zero R] [reflected R] : expr → list R → tactic (list R)
meta def reify_poly_aux : expr → list ℚ → tactic (list ℚ) -- TODO maybe use ring_m.eval instead
| `(tactic.ring.horner %%a %%x %%n %%b) l := do
  A ← reify_poly_aux a [],
  N ← tactic.eval_expr ℕ n,
  B ← expr.to_rat b,
  return (add (list.repeat 0 N ++ A) [B]) -- this should also be a function TODO
| e _ := do
  t ← expr.to_rat e, return [t]

-- meta def reify_poly (R : Type*) [has_add R] [has_zero R] [reflected R] (p : expr) :
meta def reify_poly (p : expr) : tactic (list ℚ) :=
reify_poly_aux p []

open tactic

open has_sageify has_from_sage
def sage_filename := "sagetmp.sage"
-- run_cmd
-- (unsafe_run_io $ do
--     i ← io.proc.spawn sage_io_config',
--     io.fs.put_str_ln i.stdin "1",
--     io.fs.put_str_ln i.stdin sformat!"exit()",
--     io.fs.flush i.stdin,
--     (do 0 ← io.proc.wait i, return ()) <|>
--       io.fail ("Sage produced an error, is it accessible with the " ++
--                "commands specified in `sage_io_config`?"),
--     s ← io.fs.get_line i.stdout,
--     io.fs.close i.stdin,
--     io.print_ln s.to_string)

run_cmd
  unsafe_run_io $ do
    han ← io.mk_file_handle sage_filename io.mode.write,
    let q := sageify (2/4 : ℚ),
    io.fs.put_str_ln han sformat!"print({q})",
    -- let q := sageify (polynomial.X ^ 2 - 1 : polynomial ℚ),
    -- let q := sageify (polynomial.X ^ 2 - 1 : polynomial ℚ),
    io.fs.put_str_ln han sformat!"print(list(PolynomialRing(Rationals(),'x')([1,0,-1]).factor()))",
    io.fs.flush han,
    i ← io.proc.spawn ({args := sage_config.args ++ [sage_filename], ..sage_config} : io.process.spawn_args),
    -- i ← io.proc.spawn ({args := sage_config.args ++ ["-c", "print\\(1\\)"], ..sage_config} : io.process.spawn_args),
    -- i ← io.proc.spawn ({args := sage_config.args ++ ["-c", "\"" ++ escape sage_cmd ++ "\""], ..sage_config} : io.process.spawn_args),
    io.fs.close han,
    s ← io.fs.get_line i.stdout,
    io.print_ln (ifrom_sage $ (buffer.to_string s).pop_back : ℚ),
    s ← io.fs.get_line i.stdout,
    io.print_ln (buffer.to_string s)
    -- io.print_ln (to_string $`((ifrom_sage $ (buffer.to_string s).pop_back : list (polynomial ℚ × ℕ)).head.1))
    -- io.print_ln ((from_sage $ (buffer.to_string s).pop_back : list (polynomial ℚ × ℕ)))

-- run_cmd
--   unsafe_run_io $ do
--     i ← io.proc.spawn
--   { cmd := "conda",
--     args := ["run", "-n", "sage", "--no-capture-output", "sage", "-q"
--       -- "--simple-prompt" -- unclear if helpful
--       ],
--     stdin := io.process.stdio.piped,
--     -- stderr := io.process.stdio.piped,
--     stdout := io.process.stdio.piped
--     },
--     let q := sageify (2/4 : ℚ),
--     io.fs.put_str_ln i.stdin "'t'",
--     -- -- let q := sageify (polynomial.X ^ 2 - 1 : polynomial ℚ),
--     -- let q := sageify (polynomial.X ^ 2 - 1 : polynomial ℚ),
--     io.fs.put_str_ln i.stdin sformat!"list(map(lambda x : (list(x[0]), x[1]), list(PolynomialRing(Rationals(),'x')([1,0,-1]).factor())))",
--     io.fs.put_str_ln i.stdin sformat!"exit()",
--     io.fs.flush i.stdin,
--     n ← io.proc.wait i,
--     io.print_ln n,
--     s ← io.fs.get_line i.stdout,
--     io.print_ln (s.drop 6).pop_back.to_string,
--     s ← io.fs.get_line i.stdout,
--     io.print_ln (s.drop 6).pop_back.to_string,
--     io.print_ln (from_sage $ (s.drop 6).pop_back.to_string : list (list ℚ × ℕ)),
--     io.fs.close i.stdin
meta def fac_to_expr (l : list (list ℚ × ℕ)) : tactic expr :=
do
  (fs : list expr) ← l.mmap (λ lin, do
    ((ine, _) : expr × nat) ← lin.1.mfoldl
      (λ ol ex, do return (`(%%ol.1 + (polynomial.C (%%(ex.reflect) : ℚ) : polynomial ℚ) * polynomial.X ^ ((%%(nat.reflect ol.2)) : nat) : polynomial ℚ), ol.2 + 1)) (`(0 : polynomial ℚ), 0),
    return `((%%ine) ^ (%%lin.2.reflect : nat) : polynomial ℚ)),
  final ← fs.mfoldl (λ ol ex, do return `((%%ol) * (%%ex) : polynomial ℚ)) `(1 : polynomial ℚ),
  trace final,
  sl ← simp_lemmas.mk_default,
  prod.fst <$> simplify sl [] final

section
setup_tactic_parser
open tactic.ring
open tactic

-- TODO catch errors :)
-- TODO multiple commands in one run
meta def get_sage_output_for_string (l : string) : tactic string :=
do
  trace "CALLING SAGE",
  unsafe_run_io $ (do
    i ← io.proc.spawn sage_io_config',
    io.fs.put_str_ln i.stdin l,
    io.fs.put_str_ln i.stdin sformat!"exit()",
    io.fs.flush i.stdin,
    (do 0 ← io.proc.wait i, return ()) <|>
      io.fail ("Sage produced an error, is it accessible with the " ++
               "commands specified in `sage_io_config`?"),
    s ← io.fs.get_line i.stdout,
    if (s.drop 13).take 10 = "----------".to_char_buffer
    then
      (do t ← io.fs.get_line i.stdout,
          t2 ← io.fs.get_line i.stdout,
          t2 ← io.fs.get_line i.stdout,
          io.fail $ "Sage errored with: " ++ (t.drop 7).to_string ++ t2.to_string)
    else return (),
-- TODO return more of the error, eg we should parse the entire traceback by looking for the second blank line? or maybe just read to end?
-- TypeError                                 Traceback (most recent call last)
-- <ipython-input-36-25a6001b137e> in <module>
-- ----> 1 R = PolynomialRing(NonNegativeIntegerSemiring(),'x', names=('x',)); (x,) = R._first_ngens(1)

-- /usr/local/Caskroom/miniconda/base/envs/sage/lib/python3.8/site-packages/sage/rings/polynomial/polynomial_ring_constructor.py in PolynomialRing(base_ring, *args, **kwds)
--     553     """
--     554     if not ring.is_Ring(base_ring):
-- --> 555         raise TypeError("base_ring {!r} must be a ring".format(base_ring))
--     556
--     557     n = -1  # Unknown number of variables

-- TypeError: base_ring Non negative integer semiring must be a ring
    io.fs.close i.stdin,
    io.print_ln s.to_string,
    return $ (s.drop 6).pop_back.to_string)


-- run_cmd (do (l : list ℚ) ← get_sage_output_for_string "[a]", skip)

section
setup_tactic_parser
#check expr.to_string
-- TODO a dependently typed version of this would be good
-- I.e. we should be able to factor integer polys with the same code that factors rational
meta def replace_certified_sage_equality
  (matcher : expr → tactic bool) -- match exprs to be converted
  (reify_type : Type*) -- the type the input should be converted to
  (reify : expr → tactic reify_type)
  (sage_input : reify_type → tactic string) -- takes the reified expr to
  (output_type : Type*) -- the type the sage output should be converted to
  [has_from_sage output_type]
  [has_to_tactic_format output_type] -- only for testing
  (convert_output : output_type → tactic expr) -- takes the output
  (validator : expr → expr → tactic (expr)) -- produces proofs that original expr agrees with the
  (naam : string)
  (wi : parse (parser.tk "with" *> parser.pexpr)?) :
  tactic unit :=
do
  g ← target,
  (oe : option expr) ← g.mfold (none : option expr) (λ sub n old, if old.is_some then return old else (do
    s ← matcher sub,
    match s with
    | tt := return (some sub)
    | ff := return old
    end)),
  trace oe,
  oe ← oe,
  (re : reify_type) ← reify oe,
  (s : string) ← (do w ← (wi.map return).get_or_else failure, w ← i_to_expr w,
    trace w,
    trace w.to_string,
    return $ (w.to_string.popn 1).popn_back 1)
    <|> sage_input re >>= (λ r, get_sage_output_for_string r <|> unsafe_run_io (run_online_sage_for_string' r)),
  let l : option output_type := from_sage s,
  l ← l,
  newe ← convert_output l,
  p ← validator oe newe,
  rewrite_target p,
  -- TODO maybe check equality here
  (guard wi.is_none >> trace (sformat!"Try this: {naam} with \"{s}\"")) <|> skip

end

/-
Examples:
-/

-- TODO fix other uses of reflect
meta def tactic.interactive.factor_nats := replace_certified_sage_equality
  (λ ex, do
    t ← infer_type ex,
    return $ t = `(nat))
  ℕ
  (λ e, e.to_nat)
  (λ n, return sformat!"print(list(ZZ({n}).factor()))")
  (list (ℕ × ℕ))
  (λ l, do
    ini ← l.mfoldl (λ ol ⟨p, n⟩, do
      P ← expr.of_nat `(ℕ) p,
      N ← expr.of_nat `(ℕ) n,
      return `((%%ol : ℕ) * (%%P : ℕ) ^ (%%N : ℕ))) `(1 : ℕ),
    sl ← simp_lemmas.mk_default,
    prod.fst <$> simplify sl [] ini)
  (λ o n, do
    (e₁', p₁) ← or_refl_conv norm_num.derive o, -- TODO use this trick in mathlib
    (e₂', p₂) ← or_refl_conv norm_num.derive n,
    trace e₁',
    trace e₂',
    is_def_eq e₁' e₂',
    mk_eq_symm p₂ >>= mk_eq_trans p₁)
  "factor_nats"

meta def tactic.interactive.factor_poly := replace_certified_sage_equality
  (λ ex, do
    t ← infer_type ex,
    return $ t = `(polynomial ℚ))
  (list ℚ)
  (λ e, do using_new_ref mk_buffer $ λ atoms,
    do
      (e, f) ← normalize' atoms reducible ring.normalize_mode.raw tt e,
      reify_poly e)
  (λ n, return
    sformat!"list(map(lambda x : (list(x[0]), x[1]), list(PolynomialRing(Rationals(),'x')({n}).factor())))")
  (list (list ℚ × ℕ))
  fac_to_expr
  (λ o n, do
    ((e₁', p₁), (e₂', p₂)) ← ring_m.run reducible n $
      prod.mk <$> eval (λ _, failed) o <*> eval (λ _, failed) n,
    trace e₁',
    trace e₂',
    is_def_eq e₁' e₂',
    mk_eq_symm p₂ >>= mk_eq_trans p₁)
  "factor_poly"

meta def reify_vec_cons_aux (R : Type*) (rei : expr → tactic R) : expr → list R → tactic (list R)
| `(@matrix.vec_cons %%a %%n %%el %%b) l := do
  A ← reify_vec_cons_aux b l,
  l ← rei el,
  return $ l :: A -- this should also be a function TODO
| `(matrix.vec_empty) _ := return []
| e _ := return []

meta def reify_vec_cons (R : Type*) (rei : expr → tactic R) (p : expr) : tactic (list R) :=
reify_vec_cons_aux R rei p []

meta def reify_mat {R : Type*} (f : expr → option R) (p : expr) : tactic (list $ list R) :=
reify_vec_cons (list R) (reify_vec_cons R (λ e, f e)) p

meta def mat_to_expr {R : Type} (ty : expr) (f : R → expr) (l : list (list R)) : pexpr := -- TODO use a pexpr here and i_to_expr_for_???
let n : expr := `(%%l.head.length.reflect : ℕ) in -- TODO change to ncols
l.reverse.enum.reverse.foldr (λ t ol,
  let a : expr := t.2.reverse.enum.reverse.foldr (λ v ol',
    let inp := f v.2 in `(@matrix.vec_cons.{0} %%ty (%%(v.1.reflect)) %%inp %%ol'))
    (`(matrix.vec_empty.{0} : fin 0 → %%ty) : expr) in
  ``(matrix.vec_cons.{0} %%a %%ol : fin (nat.succ %%(t.1.reflect)) → fin (%%n : ℕ) → %%ty))
  ``(@matrix.vec_empty.{0} $ fin %%n →  %%ty)

-- example :false :=
-- begin
--   (do m ← mk_mvar,
--   t ← infer_type m,
--   unify t `((%%(mat_to_expr [[1,1],[1,0]]) : fin 2 → fin 2 → ℚ) = %%(mat_to_expr [[1,1],[1,0]])), set_goals  [m]),

-- end

meta def tactic.interactive.rref := replace_certified_sage_equality
  (λ ex, do
    t ← infer_type ex >>= whnf <|> return `(Type), -- if infer type fails then return false
    match t with
    | `(fin %%e → fin %%f → ℚ) := return tt
    | _ := return ff
    end)
  (list (list ℚ))
  (reify_mat expr.to_rat)
  (λ n, return $
    sformat!"A = Matrix(QQ, {n}); A = A.augment(MatrixSpace(QQ, A.nrows(), A.nrows())(1), subdivide=True);" ++
      "B = A.rref(); (list(list(b) for b in B.subdivision(0,0)),list(list(b) for b in B.subdivision(0,1).inverse()))")
  (list (list ℚ) × list (list ℚ))
  (λ l, do
    n ← expr.of_nat `(ℕ) l.1.length,
    m ← expr.of_nat `(ℕ) l.1.head.length,
    m1 ← i_to_expr $ mat_to_expr `(ℚ) (λ n : ℚ, reflect n) l.1,
    m2 ← i_to_expr $ mat_to_expr `(ℚ) (λ n : ℚ, reflect n) l.2,
    return $ `(matrix.mul
      (%%m2 : matrix (fin %%n) (fin %%n) ℚ)
      (%%m1 : matrix (fin _) (fin %%m) ℚ)))
  (λ o n, do
    trace o,
    trace n,
    (e₁', p₁) ← or_refl_conv (conv.convert $ conv.interactive.norm_num []) o,
    -- sl ← simp_lemmas.mk.add_simp ``matrix.mul_fin_two,
    -- (e₂', p₂) ← or_refl_conv (λ e, do f ← simplify sl [] e, return (f.1, f.2.1)) n,
    (e₂'', p₂') ← or_refl_conv (conv.convert $ conv.interactive.norm_num []) n,
    -- good for debugging
    -- (do m ← mk_mvar,
    --   t ← infer_type m,
    --   i_to_expr ``(%%e₂'' = %%n) >>= unify t, set_goals [m]),
    is_def_eq e₁' e₂'',
    -- p₂ ← mk_eq_trans p₂ p₂',
    mk_eq_symm p₂' >>= mk_eq_trans p₁)
  "rref"


meta def tactic.interactive.hnf := replace_certified_sage_equality
  (λ ex, do
    t ← infer_type ex >>= whnf <|> return `(Type), -- if infer type fails then return false
    match t with
    | `(fin %%e → fin %%f → ℤ) := return tt
    | _ := return ff
    end)
  (list (list ℤ))
  (reify_mat expr.to_int)
  (λ n, return $
    sformat!"A = Matrix(ZZ, {n});" ++
      "B, U = A.hermite_form(transformation=True); (list(list(b) for b in B), list(list(u) for u in U.inverse()))")
  (list (list ℤ) × list (list ℤ))
  (λ l, do
    n ← expr.of_nat `(ℕ) l.1.length,
    m ← expr.of_nat `(ℕ) l.1.head.length,
    m1 ← i_to_expr $ mat_to_expr `(ℤ) (λ n : ℤ, reflect n) l.1, -- TODO fix this
    m2 ← i_to_expr $ mat_to_expr `(ℤ) (λ n : ℤ, reflect n) l.2,
    return $ `(matrix.mul
      (%%m2 : matrix (fin %%n) (fin %%n) ℤ)
      (%%m1 : matrix (fin _) (fin %%m) ℤ)))
  (λ o n, do
    (e₁', p₁) ← or_refl_conv (conv.convert $ conv.interactive.norm_num []) o,
    (e₂'', p₂') ← or_refl_conv (conv.convert $ conv.interactive.norm_num []) n,
    is_def_eq e₁' e₂'',
    mk_eq_symm p₂' >>= mk_eq_trans p₁)
  "hnf"

open_locale matrix
meta def tactic.interactive.snf := replace_certified_sage_equality
  (λ ex, do
    t ← infer_type ex >>= whnf <|> return `(Type), -- if infer type fails then return false
    match t with
    | `(fin %%e → fin %%f → ℤ) := return tt
    | _ := return ff
    end)
  (list (list ℤ))
  (reify_mat expr.to_int)
  (λ n, return $
    sformat!"A = Matrix(ZZ, {n});" ++
      "B, U, V = A.smith_form(transformation=True); [list(list(b) for b in B), list(list(u) for u in U.inverse()), list(list(v) for v in V.inverse())]")
  (list $ list (list ℤ)) -- TODO make a 3-tuple parser work and change this
  (λ l, do
    n ← expr.of_nat `(ℕ) l.head.length,
    m ← expr.of_nat `(ℕ) l.head.head.length,
    m1 ← i_to_expr $ mat_to_expr `(ℤ) (λ n : ℤ, reflect n) l.head, -- TODO fix this
    m2 ← i_to_expr $ mat_to_expr `(ℤ) (λ n : ℤ, reflect n) l.tail.head,
    m3 ← i_to_expr $ mat_to_expr `(ℤ) (λ n : ℤ, reflect n) l.tail.tail.head,
    trace ">>>>>",
    return $ `(
      (%%m2 : matrix (fin %%n) (fin %%n) ℤ) ⬝
      (%%m1 : matrix (fin _) (fin %%m) ℤ) ⬝
      (%%m3 : matrix (fin _) (fin %%m) ℤ)))
  (λ o n, do
    (e₁', p₁) ← or_refl_conv (conv.convert $ conv.interactive.norm_num []) o,
    (e₂'', p₂') ← or_refl_conv (conv.convert $ conv.interactive.norm_num []) n,
    is_def_eq e₁' e₂'',
    mk_eq_symm p₂' >>= mk_eq_trans p₁)
  "snf"

end

-- want multivariate examples too
-- example (x y : ℤ) : x * y + x * x * y + y + 1 = 0 :=
-- begin
--   ring_nf,
-- end

example : polynomial.eval 1 (polynomial.X ^ 3 - 1 : polynomial ℚ) = 0 :=
begin
  factor_poly with "[([-1, 1], 1), ([1, 1, 1], 1)]", -- TODO at loc
  simp,
end

example : ¬ nat.prime 1111 :=
begin
  factor_nats, -- TODO at loc
  simp [nat.prime_mul_iff],
end

open_locale matrix
-- TODO update to new mats
-- example {α : Type*} [comm_ring α] {a b c d e f g h i : α} :
--         ![![a, b], ![c, d]] ⬝ ![![e, f], ![g, i]] =
--        ![![a, b], ![c, d]] :=
-- begin
--   rw [matrix.mul_fin_two],
-- end
-- example :
--         ![![1, 2], ![3, 4]] ⬝ ![![4, 4,1], ![4, 4,1]] =
--        ![![4, 4,8], ![4, 4,0]] :=
-- begin
--   norm_num,
-- end

-- set_option trace.simplify true
-- set_option pp.all true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

-- example : ∃ v : fin 1 → fin 2 → ℚ, v ⬝
--         (![![1, 1, 0], ![1, 1, 0]] : matrix _ _ ℚ) = 0 :=
-- begin
--   rref,
--   simp_rw [← matrix.mul_assoc],
-- end



-- example : ∃ v : fin 1 → fin 2 → ℤ, v ⬝
--         (![![1, 1, 0], ![2, 2, 1]] : matrix _ _ ℤ) = 0 :=
-- begin
--   hnf,
--   simp_rw [← matrix.mul_assoc],
-- end

-- example : ∃ v : fin 1 → fin 2 → ℤ, v ⬝
--         (![![1, 1, 0], ![2, 2, 1]] : matrix _ _ ℤ) = 0 :=
-- begin
--   snf,
--   dsimp,
--   simp_rw [← matrix.mul_assoc],
-- end

/-
How should the sage monad look?
do
  let t : list blah := something from tactic state,
  s ← sage_compute

-/

/-
# TODO
- gcd by bezout
- ideal membership
- ideal equality/containment
  - optimal ideal basis
- factoring
- inverse in the class group
- class group structure
- class group generators
- finding local obstructions

## Harder

Certificate for non-principality of ideals
-/
