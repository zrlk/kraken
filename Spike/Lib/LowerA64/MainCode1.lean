/-
**The user `main`'s code and phase facts of a one-block `Accepted1`
program from `PlaceOK`** (AArch64): the analogue of `mainPh_ofPlaceOK`
(`Spike/Lib/LowerA64/MainPh.lean`) for A12's checks of every stack-checked
function (`Scc.Cert.Code1A64.fnCode1Ok`, `Scc.Cert.Ph1A64.fnPh1Ok`).

`mainPh1_ofPlaceOK`: on a one-block `Accepted1` program that lowers and
emits, whose output passes `PlaceOK`, `main`'s lowered body `r` (`lower1`
of the source body) is the `fi`th function `func1 main [] r` of the lowered
IR; at its context `cx` (a valid frame of at most 4095 bytes, a multiple of
16), the program holds its prologue at `bareMC.fn` and its blocks
(`blocksOk`) with their runs' phase facts (`blocksPh`, at the code labels,
every label read resolving); the prologue's `ProPh` at the runtime's
layout, and with a checked `+` the local overflow block with its `blkPh`.
The labels of the layout agree with the code labels (`lab_ofPlaceOK`).
-/
import Spike.Lib.LowerA64.MainPh
import Scc.Cert.Ph1A64
import Scc.Lower.InvProg1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (linkOf codeOf)
open Scc.Cert.Code1A64 (blocksOk spills hasAddChk ctxOf fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.Ph1A64 (blocksPh fnPh1Ok_parts fnPhF_of_fnPhAll1 fnPhF_facts)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Scc.Lower.Inv (lower1 Res1 func1)

/-- A function without parameters stores none in its prologue. -/
theorem spills_nil (c : FnCtx) : spills c [] = some [] := by
  simp [spills]

/-- **`main`'s lowered IR on a one-block `Accepted1` program** (AArch64):
`lowerAll`'s IR is the runtime functions then `func1 main [] r`, the
`rt.length`th function. -/
theorem lowerAll_accepted1main_a64 (cfg : Scc.Config) {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true)
    {e : Scc.Lower.A64.Emitted} (h : Scc.Lower.A64.lowerAll? cfg [d] = .ok e) :
    ∃ r rt, lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      (Scc.Lower.A64.lowerAll cfg [d]).low.ir =
        Scc.Lower.Inv.progOf cfg.layout rt [func1 (Scc.Lower.Names.user "main") [] r] ∧
      (func1 (Scc.Lower.Names.user "main") [] r, rt.length) ∈
        (Scc.Lower.A64.lowerAll cfg [d]).low.ir.funcs.zipIdx := by
  obtain ⟨r, rt, hr, -, hir, -⟩ := Scc.Lower.Inv.lowerIR_accepted1main cfg hd (lowerAll?_low_a64 h)
  have hir' : (Scc.Lower.A64.lowerAll cfg [d]).low.ir =
      Scc.Lower.Inv.progOf cfg.layout rt [func1 (Scc.Lower.Names.user "main") [] r] := by
    simp only [Scc.Lower.A64.lowerAll, h]
    exact hir
  refine ⟨r, rt, hr, hir', ?_⟩
  rw [hir']
  simp [Scc.Lower.Inv.progOf, List.mem_zipIdx_iff_getElem?]

/-- **`main`'s code and phase facts from `PlaceOK`** on a one-block
`Accepted1` program (see the module docstring), at the layout
`RuntimeLayout.ofPlaceOK h i` (any immediates `i`), the return address
after `scc_rt_main`'s `bl`. -/
theorem mainPh1_ofPlaceOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])
    let ir := (Scc.Lower.A64.lowerAll cfg [d]).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    let ra := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (cx : FnCtx) (r : Res1) (fi : Nat) (entry : Label),
      lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      (func1 (Scc.Lower.Names.user "main") [] r, fi) ∈ ir.funcs.zipIdx ∧
      cx = ctxOf ir fi (func1 (Scc.Lower.Names.user "main") [] r) ∧
      FrameOk cx ∧ cx.frame ≤ 4095 ∧ cx.frame % 16 = 0 ∧
      cx.blockLabel "entry" = .ok entry ∧
      proInC o.prog cx bareMC.fn entry = true ∧
      blocksOk o.prog cx 0 (func1 (Scc.Lower.Names.user "main") [] r).blocks = true ∧
      blocksPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (labC Λ.code.lo o.prog)
        (fun l => (codeOf Λ.code.lo o.prog l).isSome) cx ra 0
        (func1 (Scc.Lower.Names.user "main") [] r).blocks = true ∧
      (∀ l a, codeOf Λ.code.lo o.prog l = some a → Ly.lab l = Int64.ofNat a) ∧
      ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
        (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [] ∧
      (hasAddChk (func1 (Scc.Lower.Names.user "main") [] r) = true →
        Scc.Cert.Rt.A64.blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
        Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly)
          (fun _ => false) Ly.lab (Ly.lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
          A64.Abort.Local.lb = true) := by
  intro o ir Ly ra
  obtain ⟨r, rt, hr, -, hmem⟩ := lowerAll_accepted1main_a64 cfg hd hlow
  have hlab := lab_ofPlaceOK h i
  have hir := lowerAll_place_ir cfg [d]
  have hc1 := fnOk1_of_fnCode1Ok (fnCode1_of_placeOKAt h hir) hmem rfl
  obtain ⟨⟨entry, hent, hpro⟩, hle, h16, hbo, hovf, -⟩ := fnOk1_facts hc1 rfl (spills_nil _)
  obtain ⟨hra, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h hir)
  have hF := fnPhF_of_fnPhAll1 hall hmem rfl
  obtain ⟨-, rsc, rpro, hpp, hbp, hovp⟩ := fnPhF_facts hF (spills_nil _)
  rw [labC_eq hlab hra] at hbp
  have hpr := List.all_eq_true.mp rpro
  have e := fun (blk : List Directive)
      (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt (ctxOf ir rt.length
        (func1 (Scc.Lower.Names.user "main") [] r)).frame)
        (proL (ctxOf ir rt.length (func1 (Scc.Lower.Names.user "main") [] r))) []) =>
    (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
      (blkLabs blk).all (fun l => (codeOf Λ.code.lo o.prog l).isSome) = true)
  refine ⟨_, r, rt.length, entry, hr, hmem, rfl, fnCtx_frameOk .., hle, h16, hent,
    user_main_eq_bareMC_fn ▸ hpro, hbo, hbp, hlab, ?_, ?_⟩
  · apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpp ⊢
    rw [labC_eq hlab rsc] at hpp
    obtain ⟨⟨⟨⟨hd', ld1⟩, ld2⟩, br⟩, frr⟩ := hpp
    refine ⟨⟨⟨⟨?_, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd'
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact br
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro ha
    obtain ⟨rab, rlb, hb⟩ := hovp ha
    rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
    exact ⟨hovf ha, hb⟩

end Spike.Lib.LowerA64
