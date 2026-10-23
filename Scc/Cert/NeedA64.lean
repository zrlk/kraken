import Kraken.AArch64.Syntax

/-!
# The stack need table of an AArch64 program, checked on its text (G6)

`Scc.Lower.stackNeed` computes, for every stack-checked function `f` of a
program, its frame below the entry stack pointer and its **need**: the most
stack bytes it uses below its entry stack pointer until it returns (its
frame, then the deepest chain of calls of stack-checked functions after
it; a tail call needs no more than its callee).  A code check file states
the table (`{pfx}Need`: label, frame, need) and checks it on the program
the canonical loader reads (`needOk`, by `decide +kernel`):

* every `bl g` in `f`'s code, `g` in the table and not a thread entry, has
  `frame f + need g ≤ need f`;
* every `b g` in `f`'s code (a tail call), `g` in the table and not a thread
  entry, has `need g ≤ need f`;
* every thread entry (`scc_rt_main`, and the trampolines `scc_rt_thr_*`
  that spawns start: a spawn's `bl` to one runs on the child's new stack,
  so it is no call of the parent's) is in the table with a need of at most
  `budget`, the initial stack range less `Tcb.headroom` (D3).

A function's code is the run of directives from its label to the next label
that does not start with `.L` (scc's local labels all do). With `L` the
TCB's `stackLimit` word and `sp ≥ L + need f` at the entry of `f`, every
stack check on the way finds `sp - frame ≥ L`, so the grow path is never
taken (the node invariant of the G6 instances).

The frames are the generator's claim; the node proofs, which read each
frame off the prologue's instructions, check them.
-/

namespace Scc.Cert.NeedA64


/-- A row of the table: label, frame below the entry stack pointer, need. -/
abbrev Row := String × Nat × Nat

/-- The row of label `l`. -/
def row? (tbl : List Row) (l : String) : Option Row := tbl.find? (·.1 == l)

/-- A label that starts a function's code (not one of scc's `.L` labels). -/
def isFn (l : String) : Bool := !l.startsWith ".L"

/-- The edge from `f` to `g` holds: a call (`tail = false`) needs
`frame f + need g ≤ need f`, a tail call `need g ≤ need f`; an edge from
or to a function outside the table, or to a thread entry, is not
constrained. -/
def edgeOk (tbl : List Row) (entries : List String) (f : Option String) (g : String)
    (tail : Bool) : Bool :=
  entries.contains g ||
  match f.bind (row? tbl), row? tbl g with
  | some (_, fr, nf), some (_, _, ng) => if tail then ng ≤ nf else fr + ng ≤ nf
  | _, _ => true

/-- One directive of the scan: the current function and the verdict so far. -/
def step (tbl : List Row) (entries : List String) (st : Option String × Bool) (d : Directive) :
    Option String × Bool :=
  match d with
  | .label l => (if isFn l then some l else st.1, st.2)
  | .instr ⟨_, .BL (.label g)⟩ => (st.1, st.2 && edgeOk tbl entries st.1 g false)
  | .instr ⟨_, .B (.label g)⟩ => (st.1, st.2 && edgeOk tbl entries st.1 g true)
  | _ => st

/-- **The table holds on `prog`** (see above), each thread entry of
`entries` with a need of at most `budget`. -/
def needOk (prog : Program) (tbl : List Row) (budget : Nat) (entries : List String) : Bool :=
  entries.all (fun e => match row? tbl e with
    | some (_, _, n) => n ≤ budget
    | none => false) &&
  (prog.foldl (step tbl entries) (none, true)).2

end Scc.Cert.NeedA64
