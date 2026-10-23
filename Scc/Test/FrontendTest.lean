import Scc.Frontend
import Scc.Lower.Program

/-!
# Tests of the scc frontend and lowering

Elaboration-time checks of the fragment check, the `Int` addition analysis
and the lowering of small programs.  The end-to-end tests (compile, assemble,
run) are `Scc/Test/run.sh`.
-/

namespace Scc.Test
open Scc.Frontend

/-- The frontend's verdict on a source text, as text. -/
def verdict (src : String) : String :=
  match run src with
  | .ok c =>
      let adds := c.adds.map fun s => s!"{s.x}:{if s.boundable then "boundable" else "unbounded"}"
      s!"accepted; + sites {adds}"
  | .error ds => "; ".intercalate (ds.map (·.render "t.w"))

/-- An array index bounded by the array's length: the `+` is boundable by
index facts (and still keeps its check, below). -/
def boundedSrc : String := "
def step{i, d}(a : {Loc pub Array[i+1+d] LanesU8 | ini >= i+1+d} * Int[i]) : Int =
  let (s, iv) = a
  let j = iv + 1
  ret j

def main(u : Unit) : Int =
  let x = 3
  let y = x + 4
  ret y
"

/-- info: "accepted; + sites [j:boundable, y:unbounded]" -/
#guard_msgs in #eval verdict boundedSrc

/-- info: "t.w:3:3: error: `bits msb16` is not in the accepted fragment (in 'main', binding 'v')" -/
#guard_msgs in #eval verdict "
def main(u : Unit) : Int =
  let v = bits msb16 1 2
  ret 0
"

/-- info: "t.w:2:1: error: a nullable pointer type is not in the accepted fragment (in the signature of 'f')" -/
#guard_msgs in #eval verdict "
def f(a : Ptr? pub Int) : Int =
  ret 0

def main(u : Unit) : Int =
  ret 0
"

/-- info: "t.w:3:3: error: spawn: unknown block 'nobody'" -/
#guard_msgs in #eval verdict "
def main(u : Unit) : Int =
  let t = spawn{nobody}(u)
  ret 0
"

/-- The IR function names of a lowered program. -/
def funcNames (src : String) : List String :=
  match run src with
  | .ok c => match Lower.lowerProgram {} c with
    | .ok p => p.funcs.map (·.name)
    | .error e => [s!"lowering error: {e}"]
  | .error _ => ["rejected"]

/--
info: ["scc_rt_start", "scc_rt_main", "scc_rt_alloc", "scc_rt_alloc_tcb", "scc_rt_thread_reserve", "scc_rt_thread_init",
 "scc_rt_stack_take", "scc_rt_stack_release", "scc_rt_grow", "scc_rt_print", "scc_rt_park", "scc_rt_unpark",
 "scc_rt_abort", "scc_rt_abort_overflow", "scc_rt_abort_heap", "scc_rt_abort_stack", "scc_rt_abort_write",
 "scc_rt_abort_threads", "wc_main"]
-/
#guard_msgs in #eval funcNames "
def main(u : Unit) : Int =
  ret 0
"

/-- The lowered body of a block: its instructions and terminators, one block per line. -/
def lowered (src fn : String) : List String :=
  match run src with
  | .ok c => match Lower.lowerProgram {} c with
    | .ok p => match p.funcs.find? (·.name == Lower.Names.user fn) with
      | some f => f.blocks.map fun b => s!"{b.label}: {b.insts.length} insts; {repr b.term}"
      | none => ["no such function"]
    | .error e => [s!"lowering error: {e}"]
  | .error _ => ["rejected"]

-- An unsigned fixed-width division is one IR division (no sign extension, no mask).
/-- info: ["entry: 1 insts; Scc.IR.Term.ret [Scc.IR.Operand.reg \"t%0\"]"] -/
#guard_msgs in #eval lowered "
def main(u : Unit) : Int =
  let a = cvt U64 7
  let b = cvt U64 0
  let q = fop div a b
  let r = toInt q
  ret r
" "main"

/-- The checked additions (`Inst.addChk`) in the lowering of block `fn`. -/
def addChks (src fn : String) : Nat :=
  match run src with
  | .ok c => match Lower.lowerProgram {} c with
    | .ok p => match p.funcs.find? (·.name == Lower.Names.user fn) with
      | some f => (f.blocks.flatMap (·.insts)).countP fun | .addChk .. => true | _ => false
      | none => 0
    | .error _ => 0
  | .error _ => 0

-- Index arithmetic keeps its overflow check even where index facts bound it
-- (hello-world's `printL` has the same `iv + 1` shape).
/-- info: (1, 1) -/
#guard_msgs in #eval (addChks boundedSrc "step", addChks boundedSrc "main")

-- A buffer of a literal length is rejected when a region would take 4 GiB
-- (`2^29` one-word elements, `8·2^29 = 2^32` bytes); one element fewer is
-- accepted (the allocator's `2^lenBits` bound aborts it at run time).
/-- info: "t.w:3:3: error: the buffer of 536870912 elements would take 4 GiB or more in a region, beyond the 32-bit byte offsets of its locatives (in 'main', binding 'b')" -/
#guard_msgs in #eval verdict "
def main(u : Unit) : Int =
  let b = newBuf[Int] 536870912
  ret 0
"
/-- info: "accepted; + sites []" -/
#guard_msgs in #eval verdict "
def main(u : Unit) : Int =
  let b = newBuf[Int] 536870911
  ret 0
"

-- Index literals in the types an operation names are checked too.
/-- info: "t.w:3:3: error: the index literal 18446744073709551616 does not fit in 64 bits (in 'main', binding 'z')" -/
#guard_msgs in #eval verdict "
def main(u : Unit) : Int =
  let z = newBuf[Int[18446744073709551616]] 1
  ret 0
"

/-- The lowering's verdict on an arena of `bytes` bytes, for a trivial program. -/
def arenaVerdict (bytes : Nat) : String :=
  match run "
def main(u : Unit) : Int =
  ret 0
" with
  | .ok c => match Lower.lowerProgram { layout := { heapBytes := bytes } } c with
    | .ok _ => "lowered"
    | .error m => m
  | .error _ => "rejected by the frontend"

-- The arena must stay below 4 GiB, so that no object region outgrows the
-- 32-bit offsets.
/-- info: ("lowered", "the heap arena of 4294967296 bytes is 4 GiB or more: locative offsets are 32-bit byte offsets") -/
#guard_msgs in #eval (arenaVerdict (2 ^ 32 - 16), arenaVerdict (2 ^ 32))

-- `scc --code` refuses a buffer of zero-word elements (the heap counter
-- counts source units); the compiler accepts it.
#guard (codeDiags "def main(u : Unit) : Int =\n  let b = newBuf[Unit] 3\n  ret 0\n"
  (match parse "def main(u : Unit) : Int =\n  let b = newBuf[Unit] 3\n  ret 0\n" with | .ok p => p | .error _ => [])).map (·.msg) ==
  ["a buffer of zero-word elements is outside the certified fragment of the code check (in 'main', binding 'b')"]

end Scc.Test
