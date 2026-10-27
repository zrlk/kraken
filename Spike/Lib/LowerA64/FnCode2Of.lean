/-
**Each `Accepted2` code block's placement and code facts from `PlaceOK`**
(AArch64): the twins of `fnPh1_ofPlaceOK` (`Spike/Lib/LowerA64/CallSite1.lean`)
and `fnCodeC_ofPlaceOK` (`Spike/Lib/LowerA64/BlocksC1Code.lean`) for the
compiled blocks of an `Accepted2` program (`compiled2 p`, lowered by
`lowerC2` to `func2`), the code at `CodeC2`/`BlocksCodeC2` with the call
predicate `BlC2`.

- `lowerAll?_ok_of_placeOK2`: the lowering succeeds on an output passing
  `placeOKAt` (so the statements below take no success premise).
- `fnPh2_ofPlaceOK`: on an `Accepted2` program whose output passes
  `PlaceOK`, the lowered IR is the runtime functions then
  `funcs2 p ws`, and the `j`th compiled block's function `func2 …` at its
  context `cx` has `fnPh1_ofPlaceOK`'s facts: a valid frame of at most 4095
  bytes (a multiple of 16), its prologue, its blocks (`blocksOk`), their
  runs' phase facts at every return address of the phase of the one after
  `scc_rt_main`'s `bl` (`blocksPh`), the prologue's `ProPh`, and with a
  checked `+` the local overflow block with its `blkPh`.
- `fnCodeC2_of_fnPh2`: at `fnPh2_ofPlaceOK`'s witnesses, the function's
  context places stack-map labels (`maps`), its entry block is at `CodeC2`
  from 0 and its later blocks at `BlocksCodeC2` (`codeC2_block`, the blocks'
  shape `lowerC2_resC2`).
- `fnCodeC2_ofPlaceOK`: the two together, at every return address of the
  phase of the one after `scc_rt_main`'s `bl`.
-/
import Spike.Lib.LowerA64.BlocksC2Seg
import Spike.Lib.LowerA64.CallSite1
import Spike.Lib.LowerProgC2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (blockAt labelGap)
open Scc.Cert.Code1A64 (blocksOk spills hasAddChk ctxOf fnOk1_of_fnCode1Ok fnOk1_facts blocksOk_block)
open Scc.Cert.Ph1A64 (blocksPh blocksPh_blockPh blocksPh_ra fnPh1Ok_parts fnPhF_of_fnPhAll1 fnPhF_facts)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.LowerShape (func2 paramsR BlockC2)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2 lowerAll_accepted2_a64 mem_progOf_funcs2)

/-! ## Each function's placement facts -/

set_option maxRecDepth 100000 in
/-- **The lowering succeeds on an output passing `placeOKAt`**
(`lowerAll?_ok_of_placeOKC`'s statement, here without its imports): where
`lowerAll?` fails, `lowerAll`'s output is empty and fails the check (A11). -/
theorem lowerAll?_ok_of_placeOK2 {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config}
    {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    ∃ em, Scc.Lower.A64.lowerAll? cfg p = .ok em := by
  cases he : Scc.Lower.A64.lowerAll? cfg p with
  | ok em => exact ⟨em, rfl⟩
  | error _ =>
    unfold Scc.Lower.A64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.A64.Emitted)) = false := by
      simp [placeOKAt, Checks.ok, checks, show a11 (Out.ofEmitted (default : Scc.Lower.A64.Emitted)) ⟨Λ⟩ = false
        from rfl]
    exact absurd h (by rw [h0]; decide)

/-- **Each compiled block's function's placement facts from `PlaceOK`** on
an `Accepted2` program (see the module docstring), at the layout
`RuntimeLayout.ofPlaceOK h i` (any immediates `i`): the `j`th compiled block
`d` with its lowering data `w` is the function `func2 (user d.name) (paramsR
d w.na) w.sc w.hp w.r`, the `rt.length + j`th of the IR. -/
theorem fnPh2_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    let ra := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧
      (∀ l a, codeOf Λ.code.lo o.prog l = some a → Ly.lab l = Int64.ofNat a) ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        let f := func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r
        let cx := ctxOf ir (rt.length + j) f
        LowC2 p cfg.layout.obj d w ∧ (f, rt.length + j) ∈ ir.funcs.zipIdx ∧
        FrameOk cx ∧ cx.frame ≤ 4095 ∧ cx.frame % 16 = 0 ∧
        ∃ (entry : Label) (ps : List (XReg × Int64)),
          cx.blockLabel "entry" = .ok entry ∧ spills cx f.params = some ps ∧
          prologueIn o.prog f.name (cx.local "stack_check") entry (Int64.ofInt cx.frame)
            (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true ∧
          blocksOk o.prog cx 0 f.blocks = true ∧
          (∀ ra' : Int64,
            Spike.Lib.A64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.A64.PhRec.ph Ly ra.toBitVec.toNat →
            blocksPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (labC Λ.code.lo o.prog)
              (fun l => (codeOf Λ.code.lo o.prog l).isSome) cx ra' 0 f.blocks = true) ∧
          ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
            (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) ps ∧
          (hasAddChk f = true →
            blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
            blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly)
              (fun _ => false) Ly.lab (Ly.lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
              A64.Abort.Local.lb = true) := by
  intro o ir Ly ra
  obtain ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK2 h
  obtain ⟨ws, rt, hws, -, -, hir, -⟩ := lowerAll_accepted2_a64 cfg hp hlow
  have hlab := lab_ofPlaceOK h i
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  obtain ⟨hra, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h (lowerAll_place_ir cfg p))
  refine ⟨ws, rt, hws, hir, hlab, fun j d w hd hw => ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjw, rfl⟩ := List.getElem?_eq_some_iff.mp hw
  intro f cx
  have hmem : (f, rt.length + j) ∈ ir.funcs.zipIdx := by
    show _ ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx
    rw [hir]
    exact mem_progOf_funcs2 cfg.layout rt hws j hj
  have hc1 := fnOk1_of_fnCode1Ok hc hmem rfl
  have hF := fnPhF_of_fnPhAll1 hall hmem rfl
  obtain ⟨ps, hps⟩ := spills_of_fnOk1 hc1
  obtain ⟨⟨entry, hent, hpro⟩, hle, h16, hbo, hovf, -⟩ := fnOk1_facts hc1 rfl hps
  obtain ⟨-, rsc, rpro, hpp, hbp, hovp⟩ := fnPhF_facts hF hps
  rw [labC_eq hlab hra] at hbp
  have hpr := List.all_eq_true.mp rpro
  refine ⟨hws.get j hj, hmem, fnCtx_frameOk .., hle, h16, entry, ps, hent, hps, hpro, hbo,
    fun ra' h' => blocksPh_ra h' hbp, ?_, ?_⟩
  · apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpp ⊢
    rw [labC_eq hlab rsc] at hpp
    obtain ⟨⟨⟨⟨hd', ld1⟩, ld2⟩, br⟩, frr⟩ := hpp
    have e := fun (blk : List Directive)
        (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt cx.frame) (proL cx) ps) =>
      (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
        (blkLabs blk).all (fun l => (codeOf Λ.code.lo o.prog l).isSome) = true)
    refine ⟨⟨⟨⟨?_, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd'
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact br
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro ha
    obtain ⟨rab, rlb, hb⟩ := hovp ha
    rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
    exact ⟨hovf ha, hb⟩

/-! ## Each function's code -/

section Place

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **The later blocks' code** (`BlocksCodeC2`) at `CdC` and `BlC2`, from
the function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`), each
of `lowerC2`'s shape (`blocksCodeC`'s twin). -/
theorem blocksCodeC2 (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {pre bs : List Scc.IR.Block} (hok : blocksOk prog cx 0 (pre ++ bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (pre ++ bs) = true)
    (hs : ∀ b ∈ bs, BlockC2 b) :
    BlocksCodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) lab bs := by
  intro b hb _
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : pre ++ (s ++ b :: t) = (pre ++ s) ++ b :: t := by simp only [List.append_assoc]
  rw [e] at hok hph
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  exact ⟨l, _, hl, codeC2_block hm hgap hlab (hs b hb) hc hseg hr⟩

/-- **The entry block's code** (`CodeC2` at the entry's label, numbered
from 0) from the function's `blocksOk` and `blocksPh`. -/
theorem entryCodeC2 (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} {bs : List Scc.IR.Block} {entry : Label}
    (hent : cx.blockLabel b.label = .ok entry) (hok : blocksOk prog cx 0 (b :: bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (b :: bs) = true)
    (hs : BlockC2 b) :
    CodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) 0 (lab entry) b.insts b.term := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  rw [hent] at hl; cases hl
  exact codeC2_block hm hgap hlab hs hc hseg hr

/-- **A compiled block's function's code** (`body2_segS_of`'s two code
premises): the function `func2 name ps sc hq r` of a closed form `r` of
`lowerC2`'s shape (`ResC2`), its entry block at `CodeC2` from 0 and its
later blocks at `BlocksCodeC2`, from its `blocksOk` and `blocksPh`. -/
theorem fnCodeC2 (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg}
    {entry : Label} (hent : cx.blockLabel "entry" = .ok entry)
    (hok : blocksOk prog cx 0 (func2 name ps sc hq r).blocks = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0
      (func2 name ps sc hq r).blocks = true) :
    CodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) 0 (lab entry) r.insts r.term ∧
      BlocksCodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) lab r.blocks :=
  ⟨entryCodeC2 (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hent hok hph ⟨hs.1, hs.2.1⟩,
    blocksCodeC2 (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hok hph hs.2.2⟩

end Place

/-- **A compiled block's function's code from `PlaceOK`, at
`fnPh2_ofPlaceOK`'s witnesses**: for the lowering data `ws` and runtime
functions `rt` and the `j`th compiled block's entry label, blocks and phase
facts as `fnPh2_ofPlaceOK` gives them, at the layout `RuntimeLayout.ofPlaceOK
h i`, the function's context places stack-map labels (`maps`), its entry
block is at `CodeC2` from 0 and its later blocks are at `BlocksCodeC2`. -/
theorem fnCodeC2_of_fnPh2 {cfg : Scc.Config} {p : CoreTerm.Prog}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {ws : List Low2} {rt : List Scc.IR.Func}
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws))
    {j : Nat} {d : Decl} {w : Low2} (hL : LowC2 p cfg.layout.obj d w) {entry : Label}
    (hent : (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).blockLabel "entry" = .ok entry)
    (hbo : blocksOk (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) 0
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r).blocks = true)
    {ra : Int64}
    (hbp : blocksPh (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h i))
      (labC Λ.code.lo (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog)
      (fun l => (codeOf Λ.code.lo (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog l).isSome)
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) ra 0
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r).blocks = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := RuntimeLayout.ofPlaceOK h i
    let cx := ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)
    cx.maps = true ∧
      CodeC2 cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra)
          (BlC2 o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra) 0
          (Ly.lab entry) w.r.insts w.r.term ∧
        BlocksCodeC2 cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra)
          (BlC2 o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra) Ly.lab
          w.r.blocks := by
  intro o Ly cx
  have hm : cx.maps = true := by
    show (Scc.Lower.A64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.A64.Rt.rS0 Ly)
  have hgap : ∀ a b n, labelGap o.prog a b n = true → Ly.lab b = Ly.lab a + Int64.ofNat (4 * n) :=
    fun _ _ _ hg => by rw [← hI.labOk]; exact Scc.Cert.Rt.A64.label_labelGap hI.lays hg
  exact ⟨hm, fnCodeC2 hm hgap (lab_ofPlaceOK h i) (Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2)
    hent hbo hbp⟩

/-- **Each compiled block's function's code from `PlaceOK`** on an
`Accepted2` program, at the layout `RuntimeLayout.ofPlaceOK h i` (any
immediates `i`), as `fnPh2_ofPlaceOK` numbers them: the `j`th compiled block
`d` with its lowering data `w` is the function `func2 (user d.name) (paramsR
d w.na) w.sc w.hp w.r`, whose context places stack-map labels (`maps`),
whose entry block is at `CodeC2` from 0 and whose later blocks are at
`BlocksCodeC2`, at every return address of the phase of the one after
`scc_rt_main`'s `bl`. With `fnPh2_ofPlaceOK`'s other facts, use
`fnCodeC2_of_fnPh2` at its witnesses. -/
theorem fnCodeC2_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    let ra := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        let f := func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r
        let cx := ctxOf ir (rt.length + j) f
        LowC2 p cfg.layout.obj d w ∧ cx.maps = true ∧
        ∃ entry : Label, cx.blockLabel "entry" = .ok entry ∧
          ∀ ra' : Int64,
            Spike.Lib.A64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.A64.PhRec.ph Ly ra.toBitVec.toNat →
            CodeC2 cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2 o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') 0
                (Ly.lab entry) w.r.insts w.r.term ∧
              BlocksCodeC2 cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC2 o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') Ly.lab
                w.r.blocks := by
  intro o ir Ly ra
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h i
  refine ⟨ws, rt, hws, hir, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, -, -, -, entry, -, hent, -, -, hbo, hbp, -⟩ := H j d w hd hw
  have H' := fun ra' hra => fnCodeC2_of_fnPh2 h i hir hL hent hbo (hbp ra' hra)
  exact ⟨hL, (H' ra rfl).1, entry, hent, fun ra' hra => (H' ra' hra).2⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.fnPh2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnPh2_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.fnCodeC2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2_ofPlaceOK

end Spike.Lib.LowerA64
