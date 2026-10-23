/-
**The user `main`'s code of an `Accepted0` program** (x86-64), from the
program's `PlaceOK`; the twin of `Spike/Lib/LowerA64/MainCode.lean`.

`mainCode_ofPlaceOK`: on an `Accepted0` program that lowers and emits
(`lowerAll?`), whose output at the assembler's sizes passes `PlaceOK` at a
configuration `pcfg`, `main`'s lowered body `r` (`lower0` of the source
body) is a function `func0 main r` of the lowered IR. Its frame `fr`
(`frOf`, as `emitFunc` builds it) is valid, a multiple of 16 and at most
4096 bytes. The cells hold its prologue at `bareMC.fn` (at the listing's
sizes) and its body at `entry`, and, when the body has an instruction, the
local overflow block. The code facts are `PlaceOK`'s A9
(`fnCode_of_placeOKAt`, `ovfCode_of_placeOKAt`) at the IR the output names
(`lowerAll_place_ir`); the frame and the body's shape come from `main_inv_x64`
(as `main_seg_of_placeOK`).

Where x86-64 differs from AArch64: `main` is a member of the IR's functions
(no index), the frame is `frOf` (no `fnCtx`), the prologue's cell sizes are
existential, and the overflow block is at `ovfL fr`.
-/
import Spike.Lib.LowerX64.Main
import Spike.Lib.LowerX64.Checks
import Spike.Lib.Rt.X64CodeIn

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower.Inv (lower0 Res func0)

/-- The user `main`'s symbol is the one `scc_rt_main` calls (`bareMC.fn`). -/
theorem user_main_eq_bareMC_fn : Scc.Lower.Names.user "main" = Spike.Lib.X64.Rt.bareMC.fn := by
  decide

/-- **`main`'s code from `PlaceOK`** (x86-64). -/
theorem mainCode_ofPlaceOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg [d]).low.ir
    ∃ (fr : Scc.Emit.X64.Frame) (r : Res) (entry : String),
      lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      func0 (Scc.Lower.Names.user "main") r ∈ ir.funcs ∧
      fr = frOf ir (func0 (Scc.Lower.Names.user "main") r) ∧
      FrameOk fr ∧ fr.size ≤ 4096 ∧ fr.size % 16 = 0 ∧
      (∃ zl zf z1 z2 zs, proInC o.prog fr Spike.Lib.X64.Rt.bareMC.fn entry zl zf z1 z2 zs = true) ∧
      bodyIn o.prog fr entry 0 r.insts r.ret = true ∧
      (r.insts ≠ [] → Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true) := by
  obtain ⟨r, rt, hr, -, hir, hinv⟩ := main_inv_x64 cfg hd hlow
  obtain ⟨-, hsz, h16, hsl, -, -, hI, -, -, -⟩ := hinv
  have hmem : func0 (Scc.Lower.Names.user "main") r ∈ (Scc.Lower.X64.lowerAll cfg [d]).low.ir.funcs := by
    rw [hir]; simp [Scc.Lower.Inv.progOf]
  have hnext := accepted0_next_x64 hd hr
  rw [← hir] at hsz h16 hsl
  have hle : (frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir (func0 (Scc.Lower.Names.user "main") r)).size ≤ 4096 := by
    simp only [frOf] at hsz hsl ⊢
    omega
  obtain ⟨w, hw⟩ := Scc.Lower.Inv.accepted0_ret_singleton hd hr
  obtain ⟨hpro, hbody⟩ := fnCode_of_placeOKAt h (lowerAll_place_ir cfg [d] sizes labelOffs) hmem hI hw
  refine ⟨_, r, _, hr, hmem, rfl, ⟨_, _, rfl, rfl⟩, hle, h16, ?_, hbody, fun hne =>
    ovfCode_of_placeOKAt h (lowerAll_place_ir cfg [d] sizes labelOffs) hmem hI hw hne⟩
  rw [← user_main_eq_bareMC_fn]; exact hpro

end Spike.Lib.LowerX64
