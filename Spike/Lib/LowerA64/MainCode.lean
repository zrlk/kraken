/-
**The user `main`'s code of an `Accepted0` program** (AArch64), from the
program's `PlaceOK`: the facts about `main`'s lowered function and its code
that `a64_start_segW` takes.

`mainCode_ofPlaceOK`: on an `Accepted0` program that lowers and emits
(`lowerAll?`), whose output passes `PlaceOK` at a configuration `pcfg`,
`main`'s lowered body `r` (`lower0` of the source body) is the `fi`th
function `func0 main r` of the lowered IR. Its context `cx` (`fnCtx` at the
IR) has a valid frame of at most 4095 bytes that is a multiple of 16; the
program holds its prologue at `bareMC.fn` and its body at `entry`; and, when
the body has an instruction, it holds the local overflow block. The code
facts are `PlaceOK`'s A9 (`fnCode_of_placeOKAt`, `ovfCode_of_placeOKAt`) at the
IR the output names (`lowerAll_place_ir`). The context and the body's shape
come from `main_inv_a64`. `mainBody_shape` exports the body's shape
(one returned word, only checked `+`s).
-/
import Spike.Lib.LowerA64.Checks
import Spike.Lib.Rt.A64CodeIn
import Scc.Cert.PlaceDataA64
import Scc.Lower.InvBodyA64

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Lower.Inv (lower0 Res func0)

/-- The user `main`'s symbol is the one `scc_rt_main` calls (`bareMC.fn`). -/
theorem user_main_eq_bareMC_fn : Scc.Lower.Names.user "main" = Spike.Lib.A64.Rt.bareMC.fn := by
  decide

/-- **The shape of `main`'s lowered body** on an `Accepted0` program: one
returned word, only checked `+`s. -/
theorem mainBody_shape {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {r : Res}
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) :
    (∃ w, r.ret = [w]) ∧ ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b :=
  ⟨Scc.Lower.Inv.accepted0_ret_singleton hd hr, (Scc.Lower.Inv.lower0_insts_addChk _ _ _ _ hr).1⟩

/-- **`main`'s code from `PlaceOK`** (B1). -/
theorem mainCode_ofPlaceOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])) = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])
    let ir := (Scc.Lower.A64.lowerAll cfg [d]).low.ir
    ∃ (cx : FnCtx) (r : Res) (fi : Nat) (entry : Label),
      lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      (func0 (Scc.Lower.Names.user "main") r, fi) ∈ ir.funcs.zipIdx ∧
      cx = Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi
        (func0 (Scc.Lower.Names.user "main") r) ∧
      FrameOk cx ∧ cx.frame ≤ 4095 ∧ cx.frame % 16 = 0 ∧
      proInC o.prog cx Spike.Lib.A64.Rt.bareMC.fn entry = true ∧
      bodyIn o.prog cx entry 0 r.insts r.ret = true ∧
      (r.insts ≠ [] → Scc.Cert.Rt.A64.blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true) := by
  intro o ir
  obtain ⟨r, rt, hr, -, hir, hmem, hinv⟩ := main_inv_a64 cfg hd hlow
  obtain ⟨hfo, -, h16, -, -, -, -, hI, -, -, -, hle⟩ := hinv
  rw [← hir] at hmem hfo h16 hle
  obtain ⟨w, hw⟩ := (mainBody_shape hd hr).1
  obtain ⟨hpro, hbody⟩ := fnCode_of_placeOKAt h (lowerAll_place_ir cfg [d]) hmem hI hw
  refine ⟨_, r, rt.length, _, hr, hmem, rfl, hfo, hle, h16, ?_, hbody, fun hne =>
    ovfCode_of_placeOKAt h (lowerAll_place_ir cfg [d]) hmem hI hw hne⟩
  rw [← user_main_eq_bareMC_fn]; exact hpro

end Spike.Lib.LowerA64
