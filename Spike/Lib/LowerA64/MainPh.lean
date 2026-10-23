/-
**The user `main`'s code and phase facts from `PlaceOK`** (AArch64): the
facts `a64_start_segW` takes about `main`'s lowered function, its code
(`mainCode_ofPlaceOK`, A9's code part) together with its phase facts (A9's
phase part, `userPh_of_placeOK`), at the runtime's layout of the output
(`RuntimeLayout.ofPlaceOK`) and its phase record (`PhRec.okPc`, `PhRec.ph`).

- `lab_ofPlaceOK`: the layout's labels agree with the code labels where
  they resolve (`label_threadAt_of_codeOf`), the label map
  `userPh_of_placeOK` takes;
- `mainPh_ofPlaceOK`: `mainCode_ofPlaceOK`'s facts and, at its context,
  body and entry, the body's `bodyPhOk` with the return address after
  `scc_rt_main`'s `bl` (`bareMC.e0` plus 4), the prologue's `ProPh`, and
  for a body with an instruction the local overflow block with its `blkPh`.
-/
import Spike.Lib.LowerA64.PhOfPlaceOK
import Spike.Lib.LowerA64.MainCode
import Spike.Lib.A64PhRec

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (linkOf codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Scc.Lower.Inv (lower0 Res func0)

/-- **The layout's labels are the code labels** where they resolve. -/
theorem lab_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ∀ l a, codeOf Λ.code.lo o.prog l = some a →
      (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a :=
  fun _ _ ha => Scc.Cert.Rt.A64.label_threadAt_of_codeOf (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_above h i) ha

/-- **`main`'s code and phase facts from `PlaceOK`** (B1, P5, B2): on an
`Accepted0` program that lowers and emits, whose output passes `PlaceOK`,
`mainCode_ofPlaceOK`'s facts, and at its context `cx`, body `r` and entry
the phase facts `a64_start_segW` takes at the layout `RuntimeLayout.ofPlaceOK h i`
(any immediates `i`). -/
theorem mainPh_ofPlaceOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])
    let ir := (Scc.Lower.A64.lowerAll cfg [d]).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    ∃ (cx : FnCtx) (r : Res) (fi : Nat) (entry : Label),
      lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      (func0 (Scc.Lower.Names.user "main") r, fi) ∈ ir.funcs.zipIdx ∧
      cx = Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi
        (func0 (Scc.Lower.Names.user "main") r) ∧
      FrameOk cx ∧ cx.frame ≤ 4095 ∧ cx.frame % 16 = 0 ∧
      proInC o.prog cx bareMC.fn entry = true ∧
      bodyIn o.prog cx entry 0 r.insts r.ret = true ∧
      bodyPhOk (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (fun _ => false) Ly.lab cx
        entry r.insts r.ret (Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec) = true ∧
      ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
        (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [] ∧
      (r.insts ≠ [] → Scc.Cert.Rt.A64.blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
        Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly)
          (fun _ => false) Ly.lab (Ly.lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
          A64.Abort.Local.lb = true) := by
  intro o ir Ly
  obtain ⟨r, rt, hr, -, hir, hmem, hinv⟩ := Scc.Lower.InvA64.main_inv_a64 cfg hd hlow
  obtain ⟨hfo, -, h16, -, -, -, -, hI, -, -, -, hle⟩ := hinv
  rw [← hir] at hmem hfo h16 hle
  obtain ⟨w, hw⟩ := (mainBody_shape hd hr).1
  obtain ⟨hpro, hbody⟩ := fnCode_of_placeOKAt h (lowerAll_place_ir cfg [d]) hmem hI hw
  obtain ⟨hP, hA, hB⟩ := userPh_of_placeOK h (lowerAll_place_ir cfg [d]) (lab_ofPlaceOK h i) hmem hI hw
  refine ⟨_, r, rt.length, _, hr, hmem, rfl, hfo, hle, h16, user_main_eq_bareMC_fn ▸ hpro, hbody, hw ▸ hB, hP,
    fun hne => ⟨ovfCode_of_placeOKAt h (lowerAll_place_ir cfg [d]) hmem hI hw hne, hA hne⟩⟩

end Spike.Lib.LowerA64
