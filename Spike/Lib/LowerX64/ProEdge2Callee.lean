/-
**The prologue's edge into a plain callee's body** (x86-64): `ProEdge2`
(`Spike/Lib/LowerX64/ProgC2.lean`) at a plain call's callee entry
(`calleeN`, the entry invariant `callC2_of`'s `hcal` hands the callee, and
the one of `CalleePre2`'s `hedge` at `hcal_of`), for a code block with an
`Int` parameter (`plain2`) whose body is lowered at its parameter's
environment (`env2 d 1`) and layouts; the twin of
`Spike/Lib/LowerA64/ProEdge2Callee.lean`.

- `spillAt_param`: the parameter register has a cell (the prologue's
  spill);
- `cE_of_callTo`: the source's entry control of a call of `dg`;
- `proEdge2_ofCallee`: `ProEdge2` at `calleeN`'s invariant, from the
  stack limit's facts (`LimOk`) alone: the saved `%rbp`, the return
  address, the `%fs` base and `%rdi` from `calleeN`, the ghost the entry
  control, the body's entry node's source facts by `entry2_njB`,
  `entry2_slotRep` at the argument (`ArgV`).
-/
import Spike.Lib.LowerX64.ProEdge2Of
import Spike.Lib.Src.Entry2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Emit.X64 (argRegs)
open Spike.Lib.LowerNode
open Spike.Lib.X64.Flow (CallTo)
open Spike.Lib.X64.Flow.Ret0 (LimOk)

/-- **The parameter register of a one-word parameter has a cell** when
the prologue's spill (`spills`, any cell sizes) succeeds. -/
theorem spillAt_param {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Decl}
    {zs : List Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hs : Scc.Cert.Code1X64.spills fr (Spike.Lib.LowerShape.paramsR d 1) zs = some ps) :
    ∃ k, rsOf fr s!"{d.arg}.{0}" = some k := by
  obtain ⟨-, hz, hsp⟩ := paramSpillN_of_spills hf h1 hs
  simp only [Spike.Lib.LowerShape.paramsR, List.range_one, List.map_cons, List.map_nil, argRegs,
    List.zip_cons_cons, List.zip_nil_left, List.length_cons, List.length_nil] at hsp hz
  match zs, ps, hz, hsp with
  | [_], [_], _, ⟨⟨_, hr, _⟩, _⟩ => exact ⟨_, hr⟩

/-- **The source's entry control of a call of `dg`** (`CallTo` at the call
`let x = g a; e`, `g` naming `dg`): `dg`'s body, its parameter bound, no
hold. -/
theorem cE_of_callTo {p : Prog} {c cE : Ctl} {frm : TermRun.Frame} (h : CallTo p c cE frm) {x g : String}
    {a : At} {e : Expr} (hct : c.term = .let_ x (.call g [] a []) e) {dg : Decl}
    (hfd : p.find? (·.name == g) = some dg) :
    ∃ ws, cE = ⟨dg.body, [(dg.arg, dg.argTy, ws)], none⟩ := by
  obtain ⟨x', f, a', e', d0, t, ws0, ht, hfd0, -, hcE, -⟩ := h
  rw [hct] at ht
  cases ht
  rw [hfd] at hfd0
  cases hfd0
  exact ⟨ws0, hcE⟩

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}

/-- **The prologue's edge into a plain callee's body** (`ProEdge2` at
`calleeN`'s invariant, any `J` within it, the ghost the entry control
`q.cE`): for a code block `d` with an `Int` parameter (`hint`), its body
lowered at `env2 d 1` (`henv`) and the entry's layouts (`hlits`), its
spill `spills` at `paramsR d 1` (`hs`), at a call of it (`hcE`, e.g.
`cE_of_callTo`) with a number argument (`ArgV`), from the stack limit's
facts at each state of `J` (`hlim`). -/
theorem proEdge2_ofCallee {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hint : d.argTy = .int)
    (henv : c.env = Spike.Lib.LowerShape.env2 d 1)
    (hlits : c.lits = (Scc.Lower.params2 d).map (·, Scc.Lower.shapeOf d.argTy)) {zs : List Nat}
    (hs : Scc.Cert.Code1X64.spills c.fr (Spike.Lib.LowerShape.paramsR d 1) zs = some c.ps)
    {g : String} {tp : UInt64} {q : CallG} (harg : ArgV lbl q) {ws : List TermRun.Word}
    (hcE : q.cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩)
    {ms0 : MemSide isa} {F : MachineData → Prop} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c', J σ c' → (calleeN (_root_.Executable.labels exe).label g tp q).J σ c')
    (hlim : ∀ σ c', J σ c' →
      LimOk ms0 F (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec)
        (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt c.fr.size).toBitVec)) :
    ProEdge2 p lbl lsize ms0 F c q.fp q.ra tp q.cE J := by
  obtain ⟨k, hk⟩ := spillAt_param c.hf c.h1 hs
  obtain ⟨x, t, w, hxe, hv, n, hn, hlt⟩ := harg
  have hw : ws = [w] ∧ q.cE.env = [(d.arg, d.argTy, [w])] := by
    rw [hcE] at hxe ⊢
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hxe
    obtain ⟨rfl, rfl, rfl⟩ := hxe
    exact ⟨rfl, rfl⟩
  have hterm : q.cE.term = d.body := by rw [hcE]
  have hhold : q.cE.hold = none := by rw [hcE]
  have hW := c.hWk _ (mem_lowerEnvs2_head c.lcx c.env 0 d.body)
  have htot : ∀ y ∈ Scc.Sem.exprFv d.body, (Spike.Lib.Form.lookupS (ofEnv2 c.env) y).isSome :=
    fun y hy => isSome_lookupS_ofEnv2 (Spike.Lib.LowerShape.lowerC2_fv c.lcx d.body c.env 0 _ _ c.r c.hr y hy)
  refine proEdge2_ofSpills (na := 1) c hs fun σ c' hJσ => ?_
  obtain ⟨rfl, hfp, hra, hdi, htp⟩ := hJ σ c' hJσ
  have hl := hlim σ _ hJσ
  refine ⟨⟨hl.rt, hl.mp, hl.unmapped, hl.room⟩, hfp, hra, htp, .refl _, fun sl hsl _ => ?_⟩
  have hslk : sl k = q.v := by
    rw [hsl _ .rdi (by simp [Spike.Lib.LowerShape.paramsR, argRegs]) k hk, ← hdi]
    simp [Reg64s.get64]
  rw [henv] at htot hW ⊢
  rw [hlits]
  exact ⟨⟨fun _ => False, #[], 0, entry2_njB (B := 0) hint hterm hhold hw.2 hv ⟨n, hn, hlt⟩ hk hslk⟩,
    entry2_slotRep hint hterm hhold hw.2 hv hk hslk htot hW.2.2.2.2 hW.1⟩

end Edge

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.proEdge2_ofCallee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_ofCallee
