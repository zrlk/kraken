/-
**`main`'s return tail at the held frames, end to end** (AArch64): the
block of `main`'s `ret a` (its loads, the frame's exit, `ret`) after a held
call `let x = call g w in ret a`, one segment from the held node of its
`bodyN2` (`heldRN`, `Spike/Lib/LowerA64/Body2SegHF.lean`) to `ExitC2SLF`,
its states inside `W2` at the held frames. The pieces:

- `retHeld_seg` (`Body2SegHF.lean`): the segment from the block's `W` fact;
- `retHeld_hW` (`RetHeldW.lean`): the block's states inside `W2`, from
  - `blkW_sfacts_ret2` (`RetSFacts2.lean`): `SFacts` at the source start's
    control;
  - `retHeld_hab` (`RetHeldAb.lean`): the write abort's phase kept, `main`'s
    return address a position off the write abort (`hpos`);
  - `hx_held` (`HeldRes.lean`): the held frame's result `x` in the call's
    result cell (the call's code `hcall`, `HeldC`'s `f.x = x`, `hfx`).

So `mainTailA_seg`'s premises are the walk's facts at the `ret` (the frame,
the region, the block of the code at `main`'s return address, the returned
atom's placements and layout), at the held call (its code, the frame's
result variable) and the frame run to the held node's ghost.
-/
import Spike.Lib.LowerA64.Body2SegHF
import Spike.Lib.LowerA64.RetHeldAb
import Spike.Lib.LowerA64.HeldRes
import Spike.Lib.LowerA64.RetSFacts2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Scc.Lower.Inv (regName)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`main`'s return tail at the held frames is one segment to
`ExitC2SLF`** (`retHeld_seg` at `retHeld_hW`: `SFacts` by
`blkW_sfacts_ret2`, the write abort's phase by `retHeld_hab`, the held
frame's result cell by `hx_held`). The frame `cx` and the region `R`
(`hf`, …, `hFO`); the runtime's facts (`hI`, `hpr`, `habt`); the `ret a`
block of the code at `main`'s return address `ra` (`hcd`), `ra` a position
off the write abort (`hpos`); the returned atom's placements and layout
(`hl`, …, `hera`); the held call's code (`hcall`), its result variable `x`
the held frame's (`hfx`), the continuation's symbolic environment `x` bound
to the call's result register; the frame run to the held node's ghost
`c0'` (`hr`); `W` from `W2` at the held frames (`hW₀`). -/
theorem mainTailA_seg (hp : ProgNoS ZBad p) {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL prog okPc ph lab (Int64.ofBitVec ra)) pc (directives (ls ++ cx.leave ++ [ret])))
    (hpos : PosOff prog lab (Int64.ofBitVec ra))
    {x : String} {env : Scc.Lower.Env} {nr : Nat} {a : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt (ofEnv2 ((x, .int, [.reg (regName "r" nr)]) :: env)) a = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop} {kk : Nat} {pc0 pc0' : Int64}
    {g : String} {w : Scc.IR.Operand}
    (hcall : InstsC2 cx Cd Bl kk pc0 [.call [regName "r" nr] (Scc.Lower.Names.user g) [w]] pc0')
    {fs : List TermRun.Frame} (hfx : ∀ f, fs = [f] → f.x = x)
    {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', []))
    (hW₀ : ∀ st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize st c fs → W st c fs)
    {Ab : FragS isaLSE2} :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0' pc (.ret a)
        (ofEnv2 ((x, .int, [.reg (regName "r" nr)]) :: env)) lits cs bufs).withTp tp))).at fs)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have hok := okBlk_ret2 hf h1 h16 hl
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc →
      CodeAt st pc (directives (ls ++ cx.leave ++ [ret])) :=
    SubCd.cdOf (fun _ _ h => by
      obtain ⟨-, L, j, hpc, hb, -⟩ := CdCL.toCdC h
      exact Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (by rw [hI.labOk]; exact hpc)) hcd
  have hS := blkW_sfacts_ret2 (lbl := lbl)
    (n := heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0' pc (.ret a)
      (ofEnv2 ((x, .int, [.reg (regName "r" nr)]) :: env)) lits cs bufs).withTp tp))
    hI hf h1 h16 hR hal hlo hhi hl8 hh8 hsub hfit hFO rfl
    (fun _ _ ⟨_, _, _, ⟨⟨_, hfj, _⟩, _⟩⟩ => hfj) hl (hcd.mono fun _ _ h => CdCL.toCdC h)
  have hab := retHeld_hab (p := p) (lbl := lbl) (lsize := lsize) (fs := fs) (i := i) (fp := fp) (c0 := c0')
    (t := .ret a) (s := ofEnv2 ((x, .int, [.reg (regName "r" nr)]) :: env)) (lits := lits) (cs := cs)
    (bufs := bufs) (tp := tp) (F := F) hI hpr habt hf h1 hl hcd hok hR hal hlo (by omega) hpos
  exact retHeld_seg hf h1 h16 hF hR hal hlo hhi hl hn hsa hg hsc hlit hera hcode hr fs hW₀
    (retHeld_hW hp hf h1 hl hcode hok hR hal hlo (by omega) hS hab
      (hx_held hf hcall hlo hhi hfx))

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.mainTailA_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainTailA_seg
