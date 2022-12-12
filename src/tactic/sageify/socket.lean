import system.io
import data.string.defs
import data.json
import data.buffer.parser.numeral


#eval json.parse "\"hi\\n\""
#eval json.parse "{\"hi\":\"ho\\n\"}"

def sagecell_io_config : io.process.spawn_args :=
{ cmd := "ncat",
  args := ["--ssl", "sagecell.sagemath.org", "443"],
  stdin := io.process.stdio.piped,
  stderr := io.process.stdio.piped,
  stdout := io.process.stdio.piped }

-- (printf "POST /service HTTP/1.1\r\nHost: sagecell.sagemath.org\r\nContent-type: application/x-www-form-urlencoded\r\nContent-length: 13\r\nConnection: Close\r\n\r\ncode=print(1)\r\n"; sleep 4) | openssl s_client -connect sagecell.sagemath.org:443
def sagecell_io_config' : io.process.spawn_args :=
{ cmd := "openssl",
  args := ["s_client", "-quiet", "-connect", "sagecell.sagemath.org:443", "-servername", "sagecell.sagemath.org"],
  stdin := io.process.stdio.piped,
  stderr := io.process.stdio.piped,
  stdout := io.process.stdio.piped }

-- def sagecell_io_config : io.process.spawn_args :=
-- { cmd := "openssl",
--   args := ["s_client", "-connect", "sagecell.sagemath.org:443", "-ign_eof"],
--       --     -- "--simple-prompt" -- unclear if helpful
--   stdin := io.process.stdio.piped,
--   stderr := io.process.stdio.piped,
--   stdout := io.process.stdio.piped
--   }

open io.proc

-- {"execution_count":1,"payload":[],"status":"ok","user_expressions":{}}
@[derive [non_null_json_serializable, inhabited]]
structure tmp' : Type
@[derive [non_null_json_serializable, inhabited]]
structure tmp :=
(execution_count : nat)
(payload : list string := [])
(status : option string := none)
(user_expressions : tmp')
@[derive [non_null_json_serializable, inhabited]]
structure sage_json_out :=
(stdout : option string)
(success : bool)
(execute_reply : option tmp := none)


instance : has_to_string sage_json_out := ⟨λ a , ""⟩

open tactic
run_cmd unsafe_run_io (do
  let s := "{\"execute_reply\":{\"execution_count\":1,\"payload\":[],\"status\":\"ok\",\"user_expressions\":{}},\"stdout\":\"1\\n2\\n\",\"success\":true}",
  (some j) ← pure (json.parse (s)),
  io.print_ln j,
  io.print_ln s,
  let e := (of_json sage_json_out j),
  io.print_ln e)

-- TODO this loops if no ncat
-- TODO maybe use alternative like https://www.quora.com/What-is-a-utility-like-netcat-that-supports-TLS
meta def run_online_sage_for_string (inp : string) : io string :=
do
  i ← io.proc.spawn sagecell_io_config', -- TODO urlencode input?
  io.fs.put_str_ln i.stdin
sformat!"POST /service HTTP/1.1
Host: sagecell.sagemath.org
Content-type: application/x-www-form-urlencoded
Content-length: {inp.length + 5}
Connection: Close

code={inp}
",
  io.fs.flush i.stdin,
  (o, s) ← io.iterate (ff, buffer.nil) (λ p, do s ← io.fs.get_line i.stdout,
    if p.1 then return none else do
    return (some ((buffer.to_string s).starts_with ("Content-Length: "), s))),
  parse_result.done _ n ← return ((parser.nat s) 16), -- get content length
  _ ← io.iterate () (λ _, do s ← io.fs.get_line i.stdout,
    if s.size ≤ 2 then return none else return (some ())),
  s ← io.fs.read i.stdout n,
  io.fs.close i.stdin,
  some j ← pure (json.parse (buffer.to_string s)),
  exceptional.success e ← pure (of_json sage_json_out j),
  return e.stdout.iget.pop_back

run_cmd (unsafe_run_io $ run_online_sage_for_string "print(1)
print(2)" >>= io.print )


def sagecell_io_config'' : io.process.spawn_args :=
{ cmd := "curl",
  args := ["https://sagecell.sagemath.org/service", "--data-urlencode", "code@-"],
  stdin := io.process.stdio.piped,
  stderr := io.process.stdio.piped,
  stdout := io.process.stdio.piped }

meta def run_online_sage_for_string' (inp : string) : io string :=
do
  i ← io.proc.spawn sagecell_io_config'', -- TODO urlencode input?
  io.fs.put_str_ln i.stdin inp,
  io.fs.flush i.stdin,
  io.fs.close i.stdin,
  s ← io.fs.read_to_end i.stdout,
  -- io.print_ln (buffer.to_string s),
  some j ← pure (json.parse (buffer.to_string s)),
  exceptional.success e ← pure (of_json sage_json_out j),
  return e.stdout.iget.pop_back

run_cmd (unsafe_run_io $ run_online_sage_for_string' "print(1)
print(2)" >>= io.print )
