/-
**The instruction forms a WeakCore lowering may
emit on AArch64, as one decidable predicate.**

The backward simulation from WeakCore to Kraken (the per-event and
instruction lifts of `Lower/EventsA64*.lean`) fails at a few AArch64
instruction forms, because Kraken (like herd) is weaker there than WeakCore,
or because Kraken splits the access where WeakCore does not. A lowering must
not emit them. `Instr.WCLowerable` lists them; each clause names the finding
that forces it:

1. **LSE2.** No 64-bit `LDP`/`STP`. On the `isaLSE2` route such a pair is one
   16-byte access, and the transfer from `isa` (`Lower/LSE2Transfer.lean`,
   `Lower/LSE2Final.lean`) needs `Directive.LSE2Free` of every cell.
   `Directive.WCLowerable.lse2Free` gives it, so the LSE2 route can take its
   `hfree` from `Program.WCLowerable` (`Program.WCLowerable.lse2Free`).
2. **B6/F7.** `CAS` only as `casa`/`casal` (`RmwKind.acq`/`.acqRel`). After a
   successful non-acquire `cas`/`casl`, herd (and Kraken) keep the comparand
   register's old dependencies, while WeakCore gives it the view of the value
   read; a later load addressed by that register is then ordered in WeakCore
   but not in Kraken.
3. **F6.** No no-return atomics: no `CAS` whose comparand is `XZR`/`WZR`, no
   `SWP`/`LD<op>` whose destination is `XZR`/`WZR` (so no `ST<op>`). herd
   (`aarch64hwreqs.cat:133`) does not order a no-return read by `DMB LD` and
   never treats it as an acquire; WeakCore has no no-return RMW. The test is
   the semantics' own `RegOrZr.isZr`, the `noRet` flag `MachineData.rmwK`
   receives.
4. **B3.** An acquire load is `ldar` (`LoadKind.acq`). `ldapr`
   (`LoadKind.acqPc`, RCpc) simulates only an RCpc acquire
   (`Lower/EventsA64Ldop.lean`) and stays excluded until B3 is fixed (B3:
   WeakCore forbids herd's `SB+dmb.st-rfi-acq+dmb.sy`, an acquire read of the
   thread's own write).
5. **K1.** No pair atomics: no `CASP`, and no pair exclusives `LDXP`/`STXP`.
   Kraken performs a `CASP` as two 8-byte RMWs in one step (stock herd,
   `Lower/EventsA64Pair.lean`), while WeakCore's `casPair` is one operation;
   `casPair` is not lowered on AArch64. The pair exclusives are per-half
   accesses too.
6. **Sub-word stores.** No 8- or 16-bit write: no `STRB`/`STURB`/`STRH`/
   `STURH`, and no `B`/`H` form (`MemWidth.W8`/`.W16`) of `STLR`, `STXR`,
   `CAS`, `SWP` or `LD<op>`. The lowering writes a sub-word as a word load
   plus a word store, so it never emits these; a sub-word write to a word
   location would be a mixed-size access, which Kraken rejects.

Everything else (ALU, branches, calls, plain and acquire loads of any width,
word stores, barriers, `LDXR`/`STXR` at word size) is allowed: the clauses
reject exactly the forms above and nothing more. LL/SC is not otherwise
restricted here (it is deferred in the logic, not a simulation finding).
Labels and byte arrays are lowerable.

The system-call and thread-pointer forms (`Kraken/SYSCALL.md`) are allowed and
need no clause, because none of them has a memory event:
- `MRS Xt, TPIDR_EL0` / `MSR TPIDR_EL0, Xt` are register moves between `Xt` and
  the private register `Reg64s.TPIDR_EL0` (no effect but `done`; `Operation.deps`
  gives them no address or data role in any access);
- `SVC #imm` is `MachineData.pendingSyscall`: an `unimplemented` effect, which
  the adapter makes a fault, so the thread has no event at or after it. The
  system-call step that will replace it brings its own events (trace output,
  thread creation, futex) and its own simulation obligations; this clause list
  will have to be revisited then.
On x64 (which has no twin predicate, see below) `syscall` and `ud2` are the
same halt, and
a `%fs:` move (`movfs`) is an ordinary load or store at `fsBase` plus the
operand's address, mapped-first like `mov`.

The predicates are `Bool` functions with `= true`, so `Program.WCLowerable p`
is decided by `decide` on a concrete program. `Lower/LowerablePilots.lean`
proves it, by `decide`, of every AArch64 pilot program: `pilot`
(the first lowering pilot), `pilot2` (the stack-frame pilot), `progE`/`progD` (the MS queue pilot), `allocP` (the allocation pilot),
and the fragment demos `callsDemo` (Calls) and `loopDemo` (LoopCalls).

x64 has no twin: every locked RMW is `acqRel` (no B6/F7), the x64 adapter
passes `noRet = false` (no F6), there is no RCpc load form (no B3), and a
locked `cmpxchg16b` is one 16-byte event (no K1). The sub-word convention of
clause 6 is ISA-neutral and is not encoded for x64. x64 convention note:
WeakCore RMWs must lower to locked x64 RMWs (never unlocked xadd/cmpxchg).
-/
import Kraken.AArch64.LSE2
import Kraken.AArch64.Parser

/-! ## The predicate -/

/-- A word-or-wider access size (`W32`/`W64`): not a `B`/`H` form (clause 6). -/
def MemWidth.wcWord : MemWidth → Bool
  | .W32 | .W64 => true
  | .W8 | .W16 => false

/-- A `CAS` ordering a lowering may emit: `casa` or `casal` (clause 2, B6/F7). -/
def Kraken.RmwKind.wcCasOk : Kraken.RmwKind → Bool
  | .acq | .acqRel => true
  | .plain | .rel => false

/-- **`Instr.wcLowerableB i`: `i` is a form a WeakCore lowering may emit on
AArch64** (clauses 1–6 of the module docstring). -/
def Instr.wcLowerableB : Instr → Bool
  -- (1) LSE2: no 64-bit `LDP`/`STP`.
  | ⟨.W64, .LDP ..⟩ => false
  | ⟨.W64, .STP ..⟩ => false
  -- (2) B6/F7: `casa`/`casal` only; (3) F6: comparand not `XZR`; (6) word size.
  | ⟨_, .CAS k sz rs _ _⟩ => k.wcCasOk && !rs.isZr && sz.wcWord
  -- (3) F6: destination not `XZR` (no `ST<op>`); (6) word size.
  | ⟨_, .SWP _ sz _ rt _⟩ => !rt.isZr && sz.wcWord
  | ⟨_, .LDOP _ _ sz _ rt _⟩ => !rt.isZr && sz.wcWord
  -- (4) B3: an acquire load is `ldar`, never `ldapr`.
  | ⟨_, .LDAR k _ _ _ _⟩ => k != .acqPc
  -- (5) K1: no pair atomics.
  | ⟨_, .CASP ..⟩ => false
  | ⟨_, .LDXP ..⟩ => false
  | ⟨_, .STXP ..⟩ => false
  -- (6) No sub-word stores.
  | ⟨_, .STRB ..⟩ => false
  | ⟨_, .STURB ..⟩ => false
  | ⟨_, .STRH ..⟩ => false
  | ⟨_, .STURH ..⟩ => false
  | ⟨_, .STLR sz _ _⟩ => sz.wcWord
  | ⟨_, .STXR _ sz _ _ _⟩ => sz.wcWord
  | _ => true

/-- **WeakCore-lowerable instruction** (clauses 1–6 of the module docstring). -/
def Instr.WCLowerable (i : Instr) : Prop := i.wcLowerableB = true

instance (i : Instr) : Decidable i.WCLowerable := inferInstanceAs (Decidable (_ = true))

/-- A cell's lowerability: an instruction's; labels and byte arrays are
lowerable. -/
def Directive.wcLowerableB : Directive → Bool
  | .instr i => i.wcLowerableB
  | _ => true

/-- **WeakCore-lowerable cell.** -/
def Directive.WCLowerable (d : Directive) : Prop := d.wcLowerableB = true

instance (d : Directive) : Decidable d.WCLowerable := inferInstanceAs (Decidable (_ = true))

/-- **WeakCore-lowerable program**: every cell is. -/
def Program.WCLowerable (p : Program) : Prop := ∀ d ∈ p, d.WCLowerable

instance (p : Program) : Decidable p.WCLowerable :=
  inferInstanceAs (Decidable (∀ d ∈ p, d.WCLowerable))

theorem Directive.wcLowerable_instr {i : Instr} : (Directive.instr i).WCLowerable ↔ i.WCLowerable :=
  Iff.rfl

theorem Program.wcLowerable_append {p q : Program} :
    (p ++ q).WCLowerable ↔ p.WCLowerable ∧ q.WCLowerable := by
  simp only [Program.WCLowerable, List.mem_append]
  exact ⟨fun h => ⟨fun d hd => h d (.inl hd), fun d hd => h d (.inr hd)⟩,
    fun h d hd => hd.elim (h.1 d) (h.2 d)⟩

/-! ## `WCLowerable → LSE2Free` -/

/-- **A lowerable cell has no FEAT_LSE2 reading** (clause 1). -/
theorem Directive.WCLowerable.lse2Free {d : Directive} (h : d.WCLowerable) : d.LSE2Free := by
  unfold Directive.LSE2Free
  split
  · simp [Directive.WCLowerable, Directive.wcLowerableB, Instr.wcLowerableB] at h
  · simp [Directive.WCLowerable, Directive.wcLowerableB, Instr.wcLowerableB] at h
  · simp [Directive.WCLowerable, Directive.wcLowerableB, Instr.wcLowerableB] at h
  · trivial

theorem Instr.WCLowerable.lse2Free {i : Instr} (h : i.WCLowerable) : (Directive.instr i).LSE2Free :=
  Directive.WCLowerable.lse2Free h

/-- **The LSE2 route's `hfree` from lowerability**: the form `Lower/KitLSE2.lean`
and the `*_lse2Free` lemmas use. -/
theorem Program.WCLowerable.lse2Free {p : Program} (h : p.WCLowerable) : ∀ d ∈ p, d.LSE2Free :=
  fun d hd => (h d hd).lse2Free

/-! ## Tests: each clause rejects its forms -/

section Tests
open Kraken.AArch64.Parser

/-- info: [true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval (parseAArch64("
    ldar x2, [x0]
    ldr x4, [x2, #8]
    str w9, [x1]
    stlr x1, [x0]
    casal x3, x1, [x0]
    casa w3, w1, [x0]
    swpal x1, x2, [x0]
    ldaddal x1, x2, [x0]
    ldp w1, w2, [x0]
    dmb ish
") : Program).map Directive.wcLowerableB

/-- info: [false, false, false, false, false, false, false] -/
#guard_msgs in
#eval (parseAArch64("
    ldp x1, x2, [x0]
    stp x1, x2, [x0]
    cas x3, x1, [x0]
    casl x3, x1, [x0]
    casal xzr, x1, [x0]
    swpal x1, xzr, [x0]
    stadd x1, [x0]
") : Program).map Directive.wcLowerableB

/-- info: [false, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval (parseAArch64("
    ldapr x1, [x0]
    casp x2, x3, x4, x5, [x0]
    strb w1, [x0]
    strh w1, [x0]
    stlrb w1, [x0]
    stlrh w1, [x0]
    casalb w3, w1, [x0]
    ldaddalh w1, w2, [x0]
") : Program).map Directive.wcLowerableB

-- The system-call and thread-pointer forms are lowerable.
/-- info: [true, true, true, true] -/
#guard_msgs in
#eval (parseAArch64("
    mrs x1, tpidr_el0
    msr tpidr_el0, x1
    svc #0
    ldr x2, [x1, #16]
") : Program).map Directive.wcLowerableB

example : Program.WCLowerable parseAArch64("
    msr tpidr_el0, x0
    mrs x9, tpidr_el0
    mov x8, #93
    svc #0
") := by decide

end Tests
