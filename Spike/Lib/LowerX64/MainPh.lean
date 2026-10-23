/-
**The user `main`'s code and phase facts of an `Accepted0` program**
(x86-64), from the program's `PlaceOK` (P5); the twin of
`Spike/Lib/LowerA64/MainPh.lean`.

`mainPh_ofPlaceOK`: `mainCode_ofPlaceOK`'s code facts with, at the same
frame, body, entry label and prologue cell sizes, the phase facts the user
call needs at the runtime's layout `RuntimeLayout.ofPlaceOK h i`: the
body's `bodyPhOk` (the return address `scc_rt_main`'s `.x2`, `raL`), the
prologue's `ProPh` and, when the body has an instruction, the local overflow
block's `blkPh`. The phase facts are A9's phase part (`userPh_of_placeOK`)
at the layout's labels (`hlab_ofPlaceOK`); the record's `okPc` reads the
link with the lowering's immediates, whose abort labels are the link's.

Where x86-64 differs from AArch64: the prologue's cell sizes are
existential; they are `userPh_of_placeOK`'s, stated at one witness with the
code facts.
-/
import Spike.Lib.LowerX64.MainCode
import Spike.Lib.LowerX64.PhOfPlaceOK
import Spike.Lib.Rt.X64RtPhRec

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower.Inv (lower0 Res func0)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (blkPh)
open Scc.Emit.X64 (labelOf)

/-- `scc_rt_main`'s return label after the user call is `raL`. -/
theorem bareMC_sp0 : Spike.Lib.X64.Rt.bareMC.sp0 = raL := rfl

/-- **`main`'s code and phase facts from `PlaceOK`** (x86-64, P5). -/
theorem mainPh_ofPlaceOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs
    let L := RuntimeLayout.ofPlaceOK h i
    let okPc := Spike.Lib.X64.PhRec.okPc L
    let ph := Spike.Lib.X64.PhRec.ph L
    ∃ (fr : Scc.Emit.X64.Frame) (r : Res) (entry : String) (zl zf z1 z2 zs : Nat),
      lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      FrameOk fr ∧ fr.size ≤ 4096 ∧ fr.size % 16 = 0 ∧
      proInC o.prog fr Spike.Lib.X64.Rt.bareMC.fn entry zl zf z1 z2 zs = true ∧
      bodyIn o.prog fr entry 0 r.insts r.ret = true ∧
      bodyPhOk okPc ph (fun _ => false) L.lab o.prog fr entry r.insts r.ret
        (Int64.ofBitVec (L.lab Spike.Lib.X64.Rt.bareMC.sp0).toBitVec) = true ∧
      ProPh okPc ph L.lab Spike.Lib.X64.Rt.bareMC.fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr)
        zl zf z1 z2 zs [] ∧
      (r.insts ≠ [] → Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
        blkPh okPc ph (fun _ => false) L.lab (L.lab (ovfL fr) + Int64.ofNat 0) 0
          Spike.Lib.X64.Abort.Local.lb = true) := by
  intro o L okPc ph
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
  have hpl := lowerAll_place_ir cfg [d] sizes labelOffs
  obtain ⟨-, hbody⟩ := fnCode_of_placeOKAt h hpl hmem hI hw
  obtain ⟨zl, zf, z1, z2, zs, hpro, hP, hovf, hB⟩ :=
    userPh_of_placeOK h hpl (lab := L.lab) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i) hmem hI hw
  refine ⟨frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir (func0 (Scc.Lower.Names.user "main") r), r,
    labelOf (Scc.Lower.Names.user "main") "entry", zl, zf, z1, z2, zs, hr, ⟨_, _, rfl, rfl⟩, hle, h16, ?_, hbody,
    ?_, ?_, fun hne => ⟨ovfCode_of_placeOKAt h hpl hmem hI hw hne, hovf hne⟩⟩
  · rw [← user_main_eq_bareMC_fn]; exact hpro
  · rw [hw, bareMC_sp0, Int64.ofBitVec_toBitVec]; exact hB
  · rw [← user_main_eq_bareMC_fn]; exact hP

end Spike.Lib.LowerX64
