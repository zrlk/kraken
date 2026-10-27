/-
**The code, nodes and exits of an `Accepted2` body** (x86-64): the twins
of `CodeC`, `Kind1`, `bodyN`, `ExitC` and `CallC` (`BlocksC1Code.lean`,
`Blocks1.lean`, `Node.lean`, `BodyC.lean`) over `lowerC2`'s closed form
(`Spike/Lib/LowerShapeC2.lean`); the twin of `Spike/Lib/LowerA64/Body2.lean`.

- `Kind2`: a construct's block, `Kind1`'s or a `ret` of up to six words;
- `CodeC2`, `InstsC2`, `BlocksCodeC2`: `CodeC` with two more call arms, the
  allocator's (`newBufCall`: three argument words, the result's store) and
  the output extern's (`printInsts`'s last instruction: two argument words,
  no result); `InstsC2` the arms of a run of instructions without the
  terminator, `codeC2_append` the split. A lane store's load and store and
  `printInsts`'s first four instructions are plain (`isCall` false);
- `bodyN2`, `pendN2`, `abortN2`: the nodes at the node invariant with
  buffers and slices (`NJB`, its labels, memory and label bound
  existential), indexed by the walk's layouts, known values and buffers
  (`litWalk2`, `countsB`); `bodyN`'s `NJ` asks every bound word to be a
  number, which a buffer's locative is not;
- `RetOk`, `RetJ2`, `retN2`, `ExitC2`: the exits with a return of any word
  count, each word represented by its result register (`ExitC.toC2`);
- `ContC`: a construct's exit, the node at the continuation with the walk's
  next state, or an abort;
- `CallC2`, `LaneC`, `NewBufC`, `PrintCallC`: a plain call, a lane store, a
  buffer allocation and an output call is one segment, each in `CallC`'s
  shape at `bodyN2` (its code `InstsC2`, the walk's facts `LitPt`, `EnvTy2`,
  `countsB` at the `let`). Premises of the body's induction, discharged per
  construct; `PrintCallC` is abstract over the output row.
-/
import Spike.Lib.LowerX64.BodyC
import Spike.Lib.LowerShapeC2
import Spike.Lib.Src.LowerEnvImm2Of
import Spike.Lib.LowerX64.Node2
import Spike.Lib.FrameRunM
import Spike.Lib.Src.XchgB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item emitInst emitTerm labelOf ld)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (isCall printInsts newBufCall newBufTy slotAddr xchgLoad xchgStore unitsOf refO
  countsO lowerC2 Res2)
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (atomV regName)
open Spike.Lib.Form (SEnv)
open Scc.Sem (ValRep)

/-! ## Blocks and code -/

/-- **A construct's directives** of an `Accepted2` body: `KindD`'s, or a
`ret` of the words `ws` (at most six), each loaded into its result
register (`retRegs`), then the epilogue. -/
def KindD2 (fr : Scc.Emit.X64.Frame) (ds : List Directive) : Prop :=
  KindD fr ds ∨
    ∃ (ws : List Scc.IR.Operand) (lw : List Item), ws.length ≤ Scc.Emit.X64.retRegs.length ∧
      getOps fr (ws.zip Scc.Emit.X64.retRegs) = .ok lw ∧ ds = retDirs lw

/-- **A construct's block** (sized): its directives are a construct's
(`KindD2`). -/
def Kind2 (fr : Scc.Emit.X64.Frame) (blk : List (Directive × Nat)) : Prop := KindD2 fr (blk.map (·.1))

theorem Kind2.of1 {fr : Scc.Emit.X64.Frame} {blk : List (Directive × Nat)} (h : Kind1 fr blk) : Kind2 fr blk :=
  Or.inl h

/-- **The code of a block's instructions `is` at `pc`, its label counter
at `k`, then of its terminator `tm`** (`CodeC`'s arms, and two more). The
allocator's call `call [d] scc_rt_alloc ws` (three words): `ws`'s loads
`lw` into `%rdi`, `%rsi`, `%rdx` at `pc` (`Cd`), the `callq` of `zc` bytes
after it with the return label `.L<fn>.x<k>` (`Bl`), then `%rax`'s store
into `d`'s slot `off` (`Cd`), the counter `k + 1` after it. The output
call `call [] scc_rt_print ws` (two words): `ws`'s loads into `%rdi`,
`%rsi` at `pc` (`Cd`), the `callq` with its return label (`Bl`), the
counter `k + 1` after it. -/
def CodeC2 (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) : Nat → Int64 → List Scc.IR.Inst → Scc.IR.Term → Prop
  | _, pc, [], tm => tm = .unreachable ∨
      ∃ l zs, Emits (emitTerm fr tm) l ∧ zs.length = (dirs l).length ∧ Cd pc ((dirs l).zip zs)
  | k, pc, i :: is, tm =>
    (isCall i = false ∧ ∃ l zs, Emits (emitInst fr none i) l ∧ zs.length = (dirs l).length ∧
      Cd pc ((dirs l).zip zs) ∧ CodeC2 fr Cd Bl k (pc + Int64.ofNat zs.sum) is tm) ∨
    (∃ d g w lw off zs zc z, i = .call [d] (Scc.Lower.Names.user g) [w] ∧ getOp fr .rdi w = .ok lw ∧
      rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧
      CodeC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) is tm) ∨
    (∃ d ws lw off zs zc z, i = .call [d] Scc.Lower.Names.alloc ws ∧ ws.length = 3 ∧
      getOps fr (ws.zip Scc.Emit.X64.argRegs) = .ok lw ∧
      rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧
      CodeC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) is tm) ∨
    (∃ ws lw zs zc, i = .call [] Scc.Lower.Names.print ws ∧ ws.length = 2 ∧
      getOps fr (ws.zip Scc.Emit.X64.argRegs) = .ok lw ∧
      zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.print k ∧
      CodeC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc) is tm)

/-- **The code of a run of instructions `is`** from `pc` and label counter
`k` to `pc'` and counter `k'` (`CodeC2`'s instruction arms, no terminator). -/
def InstsC2 (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) : Nat → Int64 → List Scc.IR.Inst → Nat → Int64 → Prop
  | k, pc, [], k', pc' => k' = k ∧ pc' = pc
  | k, pc, i :: is, k', pc' =>
    (isCall i = false ∧ ∃ l zs, Emits (emitInst fr none i) l ∧ zs.length = (dirs l).length ∧
      Cd pc ((dirs l).zip zs) ∧ InstsC2 fr Cd Bl k (pc + Int64.ofNat zs.sum) is k' pc') ∨
    (∃ d g w lw off zs zc z, i = .call [d] (Scc.Lower.Names.user g) [w] ∧ getOp fr .rdi w = .ok lw ∧
      rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧
      InstsC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) is k' pc') ∨
    (∃ d ws lw off zs zc z, i = .call [d] Scc.Lower.Names.alloc ws ∧ ws.length = 3 ∧
      getOps fr (ws.zip Scc.Emit.X64.argRegs) = .ok lw ∧
      rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧
      InstsC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) is k' pc') ∨
    (∃ ws lw zs zc, i = .call [] Scc.Lower.Names.print ws ∧ ws.length = 2 ∧
      getOps fr (ws.zip Scc.Emit.X64.argRegs) = .ok lw ∧
      zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.print k ∧
      InstsC2 fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc) is k' pc')

/-- **A block's code splits at a run of instructions**: the run's code to
`pc'`, counter `k'`, then the rest's. -/
theorem codeC2_append {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {tm : Scc.IR.Term} (is' : List Scc.IR.Inst) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (pc : Int64),
      CodeC2 fr Cd Bl k pc (is ++ is') tm ↔ ∃ k' pc', InstsC2 fr Cd Bl k pc is k' pc' ∧ CodeC2 fr Cd Bl k' pc' is' tm
  | [], k, pc => by
    simp only [List.nil_append, InstsC2]
    exact ⟨fun h => ⟨k, pc, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h1, h2⟩, h⟩ => h1 ▸ h2 ▸ h⟩
  | i :: is, k, pc => by
    have ih := fun k pc => codeC2_append (fr := fr) (Cd := Cd) (Bl := Bl) (tm := tm) is' is k pc
    simp only [List.cons_append, CodeC2, InstsC2, ih]
    constructor
    · rintro (⟨hc, l, zs, hE, hz, hcd, k', pc', h1, h2⟩ |
        ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, k', pc', h1, h2⟩ |
        ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, k', pc', h1, h2⟩ |
        ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, k', pc', h1, h2⟩)
      · exact ⟨k', pc', .inl ⟨hc, l, zs, hE, hz, hcd, h1⟩, h2⟩
      · exact ⟨k', pc', .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, h1⟩), h2⟩
      · exact ⟨k', pc', .inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, h1⟩)), h2⟩
      · exact ⟨k', pc', .inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, h1⟩)), h2⟩
    · rintro ⟨k', pc', (⟨hc, l, zs, hE, hz, hcd, h1⟩ |
        ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, h1⟩ |
        ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, h1⟩ |
        ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, h1⟩), h2⟩
      · exact .inl ⟨hc, l, zs, hE, hz, hcd, k', pc', h1, h2⟩
      · exact .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, k', pc', h1, h2⟩)
      · exact .inr (.inr (.inl ⟨d, ws, lw, off, zs, zc, z, hi, hn, hl, ho, hz, hcd, hb, hs, k', pc', h1, h2⟩))
      · exact .inr (.inr (.inr ⟨ws, lw, zs, zc, hi, hn, hl, hz, hcd, hb, k', pc', h1, h2⟩))

/-- **The code of a function's blocks** (`BlocksCodeC` at `CodeC2`). -/
def BlocksCodeC2 (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (lab : Label → Int64) (bs : List Scc.IR.Block) : Prop :=
  ∀ b ∈ bs, b.term ≠ .unreachable → ∃ k, CodeC2 fr Cd Bl k (lab (labelOf fr.fn b.label)) b.insts b.term

/-- `CodeC` is `CodeC2` (its arms are among `CodeC2`'s). -/
theorem codeC2_of_codeC {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (pc : Int64) (tm : Scc.IR.Term),
      CodeC fr Cd Bl k pc is tm → CodeC2 fr Cd Bl k pc is tm
  | [], _, _, _, h => h
  | _ :: is, k, pc, tm, h => by
    rcases h with ⟨hc, l, zs, hE, hz, hcd, h⟩ | ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, h⟩
    · exact .inl ⟨hc, l, zs, hE, hz, hcd, codeC2_of_codeC is _ _ _ h⟩
    · exact .inr (.inl ⟨d, g, w, lw, off, zs, zc, z, hi, hl, ho, hz, hcd, hb, hs, codeC2_of_codeC is _ _ _ h⟩)

theorem blocksCodeC2_of_blocksCodeC {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {lab : Label → Int64} {bs : List Scc.IR.Block}
    (h : BlocksCodeC fr Cd Bl lab bs) : BlocksCodeC2 fr Cd Bl lab bs := fun b hb hu =>
  (h b hb hu).imp fun _ => codeC2_of_codeC _ _ _ _

/-! ## Exits -/

/-- **A `ret` of at most six words**: at a point of the walk at `ret a`,
`a`'s words fit the result registers, each word one source word (`group`
places them one by one, no locative), as the return's exit (`RetJ2`)
puts word `j` in result register `j`. -/
def RetOk (q : Expr × Scc.Lower.Env × Nat) : Prop :=
  ∀ a, q.1 = .ret a → ∃ t ws, atomV q.2.1 a = some (t, ws) ∧ ws.length ≤ Scc.Emit.X64.retRegs.length ∧
    Spike.Lib.Form.group t ws = some (ws.map .one)

/-- **A `ret` of one word, placed as one, is of at most six words.** -/
theorem RetOne.toOk {q : Expr × Scc.Lower.Env × Nat} (h : RetOne q)
    (hg : ∀ a t w, q.1 = .ret a → atomV q.2.1 a = some (t, [w]) → Spike.Lib.Form.group t [w] = some [.one w]) :
    RetOk q := fun a ha => by
  obtain ⟨t, w, hw⟩ := h a ha
  exact ⟨t, [w], hw, by simp [Scc.Emit.X64.retRegs], hg a t w ha hw⟩

section Body2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

/-- **The body's exits at frames `fs`** for `ret`s of any word count:
`ExitC` at `retN2`. -/
def ExitC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (Ab : FragS isa) : FragS isa := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧ At exe endPc R F ((retN2 p lbl fp ra c0').withTp tp) s c) ∨
    Ab s c fs'

/-- **`ExitC` is an `ExitC2`.** -/
theorem ExitC.toC2 {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame} {Ab : FragS isa}
    {s : State} {c : Ctl} {fs' : List TermRun.Frame} (h : ExitC p lbl exe endPc R F fp ra tp c0 fs Ab s c fs') :
    ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' := by
  rcases h with ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, hL⟩, htp⟩ | h
  · exact .inl ⟨e, c0', hr.toM, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ.toJ2, hL⟩, htp⟩
  · exact .inr h

theorem ExitC2.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame} {Ab : FragS isa}
    (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2 p lbl exe endPc R F fp ra tp c0' fs Ab s c fs' →
      ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

/-- **The exit of a construct's segment** at frames `fs` (immediates table
`i`): the node at `e`
at `pc'` in `env'` (grouped, `ofEnv2`) with the walk's next layouts, known
values and buffers, the ghost `c0` run to `c0'` at `fs`; or an abort. -/
def ContC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame) (Ab : FragS isa) (pc' : Int64) (e : Expr)
    (env' : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) : FragS isa := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0' pc' e (ofEnv2 env') lits cs bufs).withTp tp) s c) ∨ Ab s c fs'

/-- **The node at a `let` of an `Accepted2` body** (`bodyN2` at `ofEnv2`,
the thread pointer `tp`, at frames `fs`). -/
abbrev LetAt (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame) (pc : Int64) (t : Expr) (env : Scc.Lower.Env)
    (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)) : FragS isa :=
  (At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0 pc t (ofEnv2 env) lits cs bufs).withTp tp)).at fs

/-! ## The constructs' segments

Each is a premise of the body's induction in `CallC`'s shape: from the node
at `let x = op in e` (the construct's instructions first in the code, from
`pc` and counter `kk` to `pc'` and `kk'`, `InstsC2`; the ghost `c0` in `G0`,
the term in `T`, the walk's facts at the `let`) to `ContC` at `e` with
`x` bound, the walk's next layouts (`opLit`), known values (`csAfter`) and
buffers (`bufsAfter`). -/

/-- **A plain call's resumption facts** at the `let` `t` at `pc` (label
counter `kk`): its closed form from `env` and counter `n` with its code and
its later blocks' (labels at `lab`), the lowering walk's facts (immediates
`i`, the term in `T`, types, grouping, register bases), the literal walk's
(`LitPt`, the calls' layouts `CallLk`, `Lk`), the pairs' counts and the
lane stores' range at the known values `cs` and buffers `bufs`. The data a
suspended caller resumes from (`BodyPtW`). -/
def PtC2 (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (lab : Label → Int64) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) (kk : Nat) (pc : Int64)
    (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (t : Expr) : Prop :=
  ∃ l k r, lowerC2 lcx env n l k t = some r ∧ CodeC2 fr Cd Bl kk pc r.insts r.term ∧
    BlocksCodeC2 fr Cd Bl lab r.blocks ∧
    (∀ q ∈ lowerEnvs2 lcx env n t, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
      LocBaseRegAt (ofEnv2 q.2.1) q.1) ∧
    (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits t, LitPt q ∧ CallLk lcx.prog q ∧ Lk q) ∧
    Scc.Lower.countsB lcx.prog cs bufs lits t = true ∧ xchgsB cs bufs t = true

/-- **A plain call** `let x = g(a)` (`CallC` at `bodyN2`): `call [r%n] g [w]`;
the call's resumption facts at the `let` (`PtC2`, the literal walk's facts
with `Lk`). -/
def CallC2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isa)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isa) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isa) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk kk' : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String)
    (a : At) (ts : List Ty) (e : Expr) (t : Ty) (w : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.call g is a ts) e) → Fresh env n →
    LitPt (.let_ x (.call g is a ts) e, lits) → EnvTy2 (.let_ x (.call g is a ts) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g is a ts) e) = true →
    Callee lcx g → atomV env a = some (t, [w]) →
    InstsC2 fr Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] kk' pc' →
    (∀ y ∈ Scc.Sem.exprFv e,
      (Spike.Lib.Form.lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e →
    PtC2 lcx fr Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.call g is a ts) e) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call g is a ts) e) env lits cs bufs)
      (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .int, [.reg (regName "r" n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)))

/-- **A lane store** `let x = xchg b[j] v`: the load of the slot into `x%n`
and the store of `v`'s word `w` (`lowerC2_xchg_inv`'s data); the walk's
facts at the continuation and at the `let` itself (free variables placed,
immediates, register bases). -/
def LaneC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isa)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isa) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isa) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk kk' : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (b j v : At)
    (e : Expr) (t : Ty) (bw : List Scc.IR.Operand) (rb : Scc.IR.Reg) (o : UInt64) (tj : Ty) (iv : UInt64)
    (μ : Mode) (u : Ty) (nu mu : Nat) (tv : Ty) (w : Scc.IR.Operand) (s1 : Bool × Nat)
    (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.xchgAt b j v) e) → Fresh env n →
    LitPt (.let_ x (.xchgAt b j v) e, lits) → EnvTy2 (.let_ x (.xchgAt b j v) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.xchgAt b j v) e) = true →
    XchgB bufs b j →
    atomV env b = some (t, bw) → refO bw = some (.reg rb, .imm o) → atomV env j = some (tj, [.imm iv]) →
    Scc.Lower.bufElem t = some (μ, u) → Scc.Obj.regOf u = some (nu, mu) → atomV env v = some (tv, [w]) →
    Scc.Obj.slots u 0 0 = some [s1] →
    InstsC2 fr Cd Bl kk pc
      [xchgLoad (regName x n) (slotAddr lcx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1),
        xchgStore (slotAddr lcx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1) w] kk' pc' →
    (∀ y ∈ Scc.Sem.exprFv e,
      (Spike.Lib.Form.lookupS (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, u, [.reg (regName x n)]) :: env)) e →
    (∀ y ∈ Scc.Sem.exprFv (.let_ x (.xchgAt b j v) e), (Spike.Lib.Form.lookupS (ofEnv2 env) y).isSome) →
    ImmIn i (ofEnv2 env) (.let_ x (.xchgAt b j v) e) → LocBaseRegAt (ofEnv2 env) (.let_ x (.xchgAt b j v) e) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.xchgAt b j v) e) env lits cs bufs)
      (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e ((x, u, [.reg (regName x n)]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.xchgAt b j v)) :: lits) (Scc.Lower.csAfter x cs (.xchgAt b j v))
        (Scc.Lower.bufsAfter x cs bufs (.xchgAt b j v)))

/-- **A buffer allocation** `let x = newBuf[τ] cn`: the allocator's call
into `x%n` (`newBufCall`, `lowerC2_newBuf_inv`'s data), the buffer's words
`[x%n, 0]` (`newBufTy τ`); the allocation's resumption facts at the `let`
(`PtC2`, the literal walk's facts with `Lk`: the allocator's landing packs
the allocating frame's resumption point, `landStk_hxa`). -/
def NewBufC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isa)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isa) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isa) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk kk' : Nat) (env : Scc.Lower.Env) (n : Nat) (x : String) (cn : At) (τ : Ty)
    (e : Expr) (tk : Ty) (kv : UInt64) (en em h : Nat) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.newBuf cn τ) e) → Fresh env n →
    LitPt (.let_ x (.newBuf cn τ) e, lits) → EnvTy2 (.let_ x (.newBuf cn τ) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.newBuf cn τ) e) = true →
    atomV env cn = some (tk, [.imm kv]) → countsO lcx.obj τ = some (en, em) →
    Scc.Obj.header0 lcx.obj .array en em = some h → en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em) →
    InstsC2 fr Cd Bl kk pc [newBufCall (regName x n) h kv (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)]
      kk' pc' →
    (∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS
      (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e →
    PtC2 lcx fr Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)))

/-- **An output call** `let x = g(a)`, `g` an extern returning `Unit`:
`printInsts` from counter `n` (`lowerC2_call_inv`'s second case; `a`'s
words a slice `[b, o, m, cw]`, its offset word `o` a register, its layout
erased `g`'s parameter's, `callsOk2`), `x` of no words. Abstract over the
output row. -/
def PrintCallC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx)
    (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isa)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isa) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isa) : Prop :=
  ∀ (c0 : Ctl) (pc pc' : Int64) (kk kk' : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String)
    (a : At) (ts : List Ty) (e : Expr) (xe : String × Scc.Frontend.Extern) (dg : Decl) (t : Ty)
    (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV))
    (cs bufs : List (String × Nat)),
    G0 c0 → T (.let_ x (.call g is a ts) e) → Fresh env n →
    LitPt (.let_ x (.call g is a ts) e, lits) → EnvTy2 (.let_ x (.call g is a ts) e, env, n) → GrpL env →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g is a ts) e) = true →
    (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf dg.argTy →
    lcx.externs.find? (·.1 == g) = some xe → lcx.prog.find? (·.name == g) = some dg → dg.retTy = .unit →
    atomV env a = some (t, [b, .reg o, m, cw]) →
    InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
    (∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS (ofEnv2 ((x, .unit, []) :: env)) y).isSome) →
    ImmIn i (ofEnv2 ((x, .unit, []) :: env)) e →
    LocBaseRegAt (ofEnv2 ((x, .unit, []) :: env)) e →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call g is a ts) e) env lits cs bufs)
      (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e ((x, .unit, []) :: env)
        ((x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits) (Scc.Lower.csAfter x cs (.call g is a ts))
        (Scc.Lower.bufsAfter x cs bufs (.call g is a ts)))

end Body2

end Spike.Lib.LowerX64
