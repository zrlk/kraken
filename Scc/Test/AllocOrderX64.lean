import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.X64
import Scc.Test.Src

/-!
# The allocator's ordering, X64

`Scc/DESIGN.md` §9.0, "Fresh allocation": the proof of the memory relation
with promises relies on the runtime allocators' cursor bump
(`Scc/Lower/Runtime.lean`, `allocF`: the IR's `rmw .add`) being an
acquire-release read-modify-write (`lock xadd`). After it the target's `vrNew`
and `vwNew` reach the bump's timestamp (`Arch.tso` makes a plain RMW `acqRel`, and Kraken's `rmwPost`
applies), so every promise made before
an allocation is dead afterwards: a certified thread holds no outstanding
promise across an allocation, and a fresh cell's zero messages (source
indices above every older promise, target image the initial write) never
meet one. With a relaxed bump the one-thread simulation fails (the
counterexample in `Scc/DESIGN.md` §9.0).

These checks compile `Scc/Test/hello1.w` and `Scc/Test/hello.w` and fail if
the emitted bump of `scc_rt_alloc` or `scc_rt_alloc_tcb` is not `lock xadd`, or if
any read-modify-write anywhere in the listing is an unlocked `xadd`. (A64 and X64 are
separate files: their syntax imports clash.)
-/

namespace Scc.Test.AllocOrderX64

/-- scc's X64 listing of a source text. -/
def listing (src : String) : String :=
  match (do
      let c ← match Frontend.run src with
        | .ok c => pure c
        | .error _ => throw "frontend"
      let ir ← Lower.lowerProgram { arch := .x64 } c
      Emit.X64.emit ir : Except String String) with
  | .ok s => s
  | .error _ => ""

/-- The listings of `hello1.w` and `hello.w`. -/
def hello1 : String := listing (w_src% "Scc/Test/hello1.w")
def hello : String := listing (w_src% "Scc/Test/hello.w")

/-- The body of function `f` in `asm`: the lines after its label up to its
next `.type` or `.size` directive. -/
def body (asm f : String) : List String :=
  (((asm.splitOn "\n").dropWhile (· != s!"{f}:")).drop 1).takeWhile fun l =>
    !(l.startsWith "\t.type" || l.startsWith "\t.size")

/-- A read-modify-write line, by mnemonic. -/
def isRmw (l : String) : Bool := ["xadd", "xchg", "cmpxchg"].any fun p => (l.splitOn p).length > 1

/-- An acquire-release read-modify-write line. -/
def isAcqRel (l : String) : Bool := l.startsWith "\tlock " || l.startsWith "\txchg"

/-- The cursor bump of `f`: its body has a read-modify-write, and every one
is acquire-release. -/
def bumpAcqRel (asm f : String) : Bool :=
  let r := (body asm f).filter isRmw
  !r.isEmpty && r.all isAcqRel

/-- Every read-modify-write of the listing is acquire-release. -/
def allAcqRel (asm : String) : Bool :=
  ((asm.splitOn "\n").filter isRmw).all isAcqRel

#guard hello1 != "" && hello != ""
#guard bumpAcqRel hello1 "scc_rt_alloc" && bumpAcqRel hello1 "scc_rt_alloc_tcb"
#guard bumpAcqRel hello "scc_rt_alloc" && bumpAcqRel hello "scc_rt_alloc_tcb"
#guard allAcqRel hello1 && allAcqRel hello

-- One each: `scc_rt_alloc`'s heap counter (`scc_rt_heap_use`) is its cursor.
/--
info: [("scc_rt_alloc", ["\tlock xaddq %rax, (%rcx)"]), ("scc_rt_alloc_tcb", ["\tlock xaddq %rax, (%rcx)"])]
-/
#guard_msgs in
#eval ["scc_rt_alloc", "scc_rt_alloc_tcb"].map fun f => (f, (body hello1 f).filter isRmw)

end Scc.Test.AllocOrderX64
