/-
**The prologue's edge into the setup function's body** (x86-64): `ProEdge2`
(`Spike/Lib/LowerX64/ProgC2.lean`) at `scc_rt_main`'s call of the setup
function (the interface's entry `uN0`, `Spike/Lib/Rt/X64Main.lean`), for a
code block with a `Unit` parameter whose body is lowered at its parameter's
environment (`env2 d 0`) and layouts; the unit-parameter twin of
`proEdge2_ofCallee` (`Spike/Lib/LowerX64/ProEdge2Callee.lean`).

- `proEdge2_ofUN0`: `ProEdge2` at `uN0`'s invariant, its stack limit's
  facts from `uN0`'s own (`LimOk` at `limA g.tp` and the room `ZU` the
  frame, `limOk_fsBase`), carried to the edge's memory side and frame
  condition (`hms`, `hFF`): the saved `%rbp`, the return address, the `%fs`
  base from `uN0`, the ghost the entry control, the body's entry node's
  source facts by `entry2U_njB`, `entry2U_slotRep`.
-/
import Spike.Lib.LowerX64.ProEdge2Callee
import Spike.Lib.LowerX64.LimOk0
import Spike.Lib.Src.Entry2U

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG limA)

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}

/-- **The prologue's edge into the setup function's body** (`ProEdge2` at
`uN0`'s invariant, any `J` within it, the ghost's saved pair, thread
pointer and entry control `g.c0`): for a code block `d` with a `Unit`
parameter (`hu`), its body lowered at `env2 d 0` (`henv`) and the entry's
layouts (`hlits`), its spill `spills` at `paramsR d 0` (`hs`), at the
entry control binding the parameter to no words (`hcE`), the room `ZU` the
frame (`hZU`); the limit word's facts `uN0` holds at its memory side `ms0`
and frame condition `F` carried to the edge's `ms1` and `F'` (`hms`,
`hFF`). -/
theorem proEdge2_ofUN0 {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hu : d.argTy = .unit)
    (henv : c.env = Spike.Lib.LowerShape.env2 d 0)
    (hlits : c.lits = (Scc.Lower.params2 d).map (·, Scc.Lower.shapeOf d.argTy)) {zs : List Nat}
    (hs : Scc.Cert.Code1X64.spills c.fr (Spike.Lib.LowerShape.paramsR d 0) zs = some c.ps)
    {g : WcG} (hcE : g.c0 = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    {lab : Label → Int64} {ms0 ms1 : MemSide isa} {F F' : MachineData → Prop} {fn : Label} {ZU : Int64}
    (hZU : ZU = Int64.ofInt c.fr.size)
    (hms : ∀ a Z, LimOk ms0 F a Z → LimOk ms1 F a Z) (hFF : ∀ m, F' m → F m)
    {J : AS → Ctl → Prop} (hJ : ∀ σ c', J σ c' → (Spike.Lib.X64.Rt.uN0 lab ms0 F fn ZU g).J σ c') :
    ProEdge2 p lbl lsize ms1 F' c g.fp g.ra g.tp g.c0 J := by
  have hterm : g.c0.term = d.body := by rw [hcE]
  have hhold : g.c0.hold = none := by rw [hcE]
  have henv0 : g.c0.env = [(d.arg, d.argTy, [])] := by rw [hcE]
  have hW := c.hWk _ (mem_lowerEnvs2_head c.lcx c.env 0 d.body)
  have htot : ∀ y ∈ Scc.Sem.exprFv d.body, (Spike.Lib.Form.lookupS (ofEnv2 c.env) y).isSome :=
    fun y hy => isSome_lookupS_ofEnv2 (Spike.Lib.LowerShape.lowerC2_fv c.lcx d.body c.env 0 _ _ c.r c.hr y hy)
  refine proEdge2_ofSpills (na := 0) c hs fun σ c' hJσ => ?_
  obtain ⟨⟨rfl, hfp, hra, hsp, htp⟩, hlim⟩ := hJ σ c' hJσ
  have hl := (hms _ _ hlim).mono hFF
  have hl' := limOk_fsBase (σ := σ) htp hl
  rw [← hsp, hZU] at hl'
  refine ⟨⟨hl'.rt, hl'.mp, hl'.unmapped, hl'.room⟩, hfp, hra, htp, .refl _, fun sl _ _ => ?_⟩
  rw [henv] at htot hW ⊢
  rw [hlits]
  exact ⟨⟨fun _ => False, #[], 0, entry2U_njB (B := 0) hu hterm hhold henv0⟩,
    entry2U_slotRep hu hterm hhold henv0 htot hW.2.2.2.2 hW.1⟩

end Edge

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.proEdge2_ofUN0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proEdge2_ofUN0
