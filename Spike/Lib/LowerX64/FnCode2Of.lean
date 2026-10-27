/-
**Each `Accepted2` code block's placement facts from `PlaceOK`** (x86-64):
the twin of `Spike/Lib/LowerA64/FnCode2Of.lean`, `fnPh1_ofPlaceOK`
(`Spike/Lib/LowerX64/CallSite1.lean`) for the compiled blocks of an
`Accepted2` program (`compiled2 p`, lowered by `lowerC2` to `func2`).

- `lowerAll?_ok_of_placeOK2`: the lowering succeeds on an output passing
  `placeOKAt` (so the statements below take no success premise).
- `fnPh2_ofPlaceOK`: on an `Accepted2` program whose output passes
  `PlaceOK`, the lowered IR is the runtime functions then `funcs2 p ws`,
  and the `j`th compiled block's function `f := func2 …`, numbered from `n`
  (`starts`), at its frame `fr := frOf ir f`, has `fnPh1_ofPlaceOK`'s facts:
  valid, a multiple of 16, below `2^31`, its prologue (at the listing's
  cell sizes, with its parameters' stores `ps`), its blocks (`blocksOk`),
  their runs' phase facts at every return address of the phase of `raL`
  (`blocksPh`), the prologue's `ProPh`, and with a checked `+` the local
  overflow block with its `blkPh`.
- `fnCodeC2_of_fnPh2`: at `fnPh2_ofPlaceOK`'s witnesses, the function's
  frame records stack maps (`maps`), its entry block is at `CodeC2` from `n`
  and its later blocks at `BlocksCodeC2` (`codeC2_block`, the blocks' shape
  `lowerC2_resC2`), the call predicate `BlC2`; the twin of
  `fnCodeC_of_fnPh1` (`Spike/Lib/LowerX64/BlocksC1Code.lean`).
- `fnCodeC2_ofPlaceOK`: the two together, at every return address of the
  phase of `raL`.
-/
import Spike.Lib.LowerX64.CallSite1
import Spike.Lib.LowerX64.LowerProgC2X
import Spike.Lib.LowerX64.BlocksC2Seg

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Emit.X64 (Frame labelOf)
open Scc.Cert.Code1X64 (blocksOk spills hasAddChk chkL starts fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.Ph1X64 (blocksPh blocksPh_ra fnPh1Ok_parts fnPhF_of_fnPhAll1 fnPhF_facts)
open Spike.Lib.X64.Flow (prologueIn)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (blkPh)
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.LowerShape (func2 paramsR BlockC2)
open Scc.Cert.Rt.X64 (labelGap)
open Scc.Cert.Ph1X64 (blocksPh_blockPh)
open Scc.Cert.Code1X64 (blocksOk_block)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2 lowerAll_accepted2_x64 mem_progOf_funcs2)

/-- **The lowering succeeds on an output passing `placeOKAt`**
(`lowerAll?_ok_of_placeOKC`'s statement, here without its imports): where
`lowerAll?` fails, `lowerAll`'s output is empty and fails the check (A11). -/
theorem lowerAll?_ok_of_placeOK2 {cfg : Scc.Config} {p : Prog} {sizes : List Nat}
    {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    ∃ em, Scc.Lower.X64.lowerAll? cfg p = .ok em := by
  cases he : Scc.Lower.X64.lowerAll? cfg p with
  | ok em => exact ⟨em, rfl⟩
  | error _ =>
    unfold Scc.Lower.X64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.X64.Emitted) sizes labelOffs) = false :=
      placeOKAt_eq_false_of_a11 rfl
    exact absurd h (by rw [h0]; decide)

/-- **Each compiled block's function's placement facts from `PlaceOK`** on
an `Accepted2` program (see the module docstring), at the layout
`RuntimeLayout.ofPlaceOK h i` (any immediates `i`): the `j`th compiled block
`d` with its lowering data `w` is the function `func2 (user d.name) (paramsR
d w.na) w.sc w.hp w.r`, the `rt.length + j`th of the IR. -/
theorem fnPh2_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    let L := RuntimeLayout.ofPlaceOK h i
    let okPc := Spike.Lib.X64.PhRec.okPc L
    let ph := Spike.Lib.X64.PhRec.ph L
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧
      (∀ l a, codeLabel Λ.code.lo o.prog l = some a → L.lab l = Int64.ofNat a) ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        let f := func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r
        let fr := frOf ir f
        LowC2 p cfg.layout.obj d w ∧ (f, rt.length + j) ∈ ir.funcs.zipIdx ∧
        ∃ (n zl zf z1 z2 zs : Nat) (zps : List Nat) (ps : List (Reg64 × Int64 × Nat)),
          (f, n) ∈ starts ir 0 ir.funcs ∧
          FrameOk fr ∧ fr.size < 2 ^ 31 ∧ fr.size % 16 = 0 ∧
          sizesAt o.prog (chkL f) 0 (5 + f.params.length) = zl :: zf :: z1 :: z2 :: zs :: zps ∧
          spills fr f.params zps = some ps ∧
          prologueIn o.prog f.name (chkL f) (labelOf f.name "entry") (Int64.ofInt fr.size)
            (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps = true ∧
          blocksOk o.prog fr n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) = true ∧
          (∀ ra' : Int64, ph ra'.toBitVec.toNat = ph (L.lab raL).toBitVec.toNat →
            blocksPh okPc ph (labC Λ.code.lo o.prog) (fun l => (codeLabel Λ.code.lo o.prog l).isSome)
              o.prog fr ra' n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) = true) ∧
          ProPh okPc ph L.lab f.name (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr)
            zl zf z1 z2 zs ps ∧
          (hasAddChk f = true →
            Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
            blkPh okPc ph (fun _ => false) L.lab (L.lab (ovfL fr) + Int64.ofNat 0) 0
              Spike.Lib.X64.Abort.Local.lb = true) := by
  intro o ir L okPc ph
  obtain ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK2 h
  obtain ⟨ws, rt, hws, -, -, hir, -⟩ := lowerAll_accepted2_x64 cfg hp hlow
  have hlab : ∀ l a, codeLabel Λ.code.lo o.prog l = some a → L.lab l = Int64.ofNat a :=
    Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i
  have hirP := lowerAll_place_ir cfg p sizes labelOffs
  have hc := fnCode1_of_placeOKAt h hirP
  obtain ⟨hra, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h hirP)
  refine ⟨ws, rt, hws, hir, hlab, fun j d w hd hw => ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjw, rfl⟩ := List.getElem?_eq_some_iff.mp hw
  intro f fr
  have hmem : (f, rt.length + j) ∈ ir.funcs.zipIdx := by
    show _ ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs.zipIdx
    rw [hir]
    exact mem_progOf_funcs2 cfg.layout rt hws j hj
  have hmemF : f ∈ ir.funcs := by
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    exact List.mem_of_getElem? hmem
  obtain ⟨n, hn⟩ := mem_starts ir 0 hmemF
  have hc1 := fnOk1_of_fnCode1Ok hc hn rfl
  obtain ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩ := fnOk1_sizes hc1
  obtain ⟨-, hpro, hlt, h16, hbo, hovf, -⟩ := fnOk1_facts hc1 rfl hz hps
  have hF := fnPhF_of_fnPhAll1 hall hn rfl
  obtain ⟨rfn, rsc, rpro, hpp, hbp, hovp⟩ := fnPhF_facts hF hz hps
  rw [labC_eq hlab hra] at hbp
  have hpr := List.all_eq_true.mp rpro
  have e := fun (blk : List (Directive × Nat))
      (hsub : ∀ L ∈ blkLabs blk, L ∈ proLabs (Int64.ofInt fr.size) (proL fr) zl z1 z2 zs ps) =>
    (List.all_eq_true.mpr fun L hL => hpr L (hsub L hL) :
      (blkLabs blk).all (fun l => (codeLabel Λ.code.lo o.prog l).isSome) = true)
  refine ⟨hws.get j hj, hmem, n, zl, zf, z1, z2, zs, zps, ps, hn, ⟨_, _, rfl, rfl⟩, hlt, h16, hz, hps,
    hpro, hbo, fun ra' h' => blocksPh_ra h' hbp, ?_, ?_⟩
  · apply proPh_of_proPhOk
    simp only [proPhOk, Bool.and_eq_true, beq_iff_eq] at hpp ⊢
    rw [labC_eq hlab rfn, labC_eq hlab rsc] at hpp
    obtain ⟨⟨⟨⟨⟨hd', lea⟩, ld1⟩, ld2⟩, cmp⟩, frr⟩ := hpp
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ld1⟩, ld2⟩, ?_⟩, ?_⟩
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact hd'
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact lea
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact cmp
    · rw [← blkPh_labC hlab (e _ fun L hL => by simp [proLabs, hL])]; exact frr
  · intro ha
    obtain ⟨rab, rlb, hb⟩ := hovp ha
    rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
    exact ⟨(hovf ha).2, hb⟩

/-! ## Each function's code -/

section Place

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64} {lo : Nat}

/-- **The later blocks' code** (`BlocksCodeC2`) at `CdC` and `BlC2`, from
the function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`, each
with its stack maps `G b`, one per instruction), each of `lowerC2`'s shape
(`blocksCodeC`'s twin). -/
theorem blocksCodeC2 (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {pre bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((pre ++ bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((pre ++ bs).map fun b => (b, G b)) = true)
    (hs : ∀ b ∈ bs, BlockC2 b) :
    BlocksCodeC2 fr (CdC cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) lab bs := by
  intro b hb _
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : (pre ++ (s ++ b :: t)).map (fun b => (b, G b)) =
      (pre ++ s).map (fun b => (b, G b)) ++ (b, G b) :: t.map (fun b => (b, G b)) := by simp
  rw [e] at hok hph
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh hph
  rw [hc] at hc'; cases hc'
  exact ⟨_, codeC2_block hm hgap hlab (hs b hb) (Nat.le_of_eq (hG b).symm) hc hseg hr⟩

/-- **The entry block's code** (`CodeC2` at the entry's label, its label
counter from `n`) from the function's `blocksOk` and `blocksPh`. -/
theorem entryCodeC2 (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {n : Nat} {b : Scc.IR.Block} {bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((b :: bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((b :: bs).map fun b => (b, G b)) = true)
    (hs : BlockC2 b) :
    CodeC2 fr (CdC cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hc] at hc'; cases hc'
  exact codeC2_block hm hgap hlab hs (Nat.le_of_eq (hG b).symm) hc hseg hr

/-- **A compiled block's function's code** (`body2_segS_of`'s two code
premises): the function `func2 name ps sc hq r` of a closed form `r` of
`lowerC2`'s shape (`ResC2`), its entry block at `CodeC2` from its label
counter `n` and its later blocks at `BlocksCodeC2`, from its `blocksOk` and
`blocksPh` with its stack maps (`callMaps`). -/
theorem fnCodeC2 (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg} {n : Nat}
    (hok : blocksOk cells fr n ((func2 name ps sc hq r).blocks.zip
      (Scc.IR.StackMap.callMaps (func2 name ps sc hq r))) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((func2 name ps sc hq r).blocks.zip (Scc.IR.StackMap.callMaps (func2 name ps sc hq r))) = true) :
    CodeC2 fr (CdC cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) n (lab (labelOf fr.fn "entry"))
        r.insts r.term ∧
      BlocksCodeC2 fr (CdC cells okPc ph lab ra) (BlC2 cells okPc ph lab fr ra) lab r.blocks := by
  obtain ⟨G, hz, hG⟩ := zip_callMaps (func2 name ps sc hq r)
  rw [hz] at hok hph
  exact ⟨entryCodeC2 (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hG hok hph ⟨hs.1, hs.2.1⟩,
    blocksCodeC2 (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hG hok hph hs.2.2⟩

end Place

/-- **A compiled block's function's code from `PlaceOK`, at
`fnPh2_ofPlaceOK`'s witnesses**: for the lowering data `ws` and runtime
functions `rt` and the `j`th compiled block's function `f` with its frame
`frOf ir f`, its label counter `n`, blocks and phase facts as
`fnPh2_ofPlaceOK` gives them, at the layout `RuntimeLayout.ofPlaceOK h i`,
the frame records stack maps (`maps`), its entry block is at `CodeC2` from
`n` and its later blocks are at `BlocksCodeC2`. -/
theorem fnCodeC2_of_fnPh2 {cfg : Scc.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {ws : List Low2} {rt : List Scc.IR.Func}
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws))
    {d : Decl} {w : Low2} (hL : LowC2 p cfg.layout.obj d w) {n : Nat}
    (hbo : blocksOk (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) n
      ((func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r).blocks.zip
        (Scc.IR.StackMap.callMaps (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r))) = true)
    {ra : Int64}
    (hbp : blocksPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i))
      (labC Λ.code.lo (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog)
      (fun l => (codeLabel Λ.code.lo (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog l).isSome)
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) ra n
      ((func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r).blocks.zip
        (Scc.IR.StackMap.callMaps (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r))) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h i
    let fr := frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)
    fr.maps = true ∧
      CodeC2 fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) n
          (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
        BlocksCodeC2 fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) Ly.lab
          w.r.blocks := by
  intro o Ly fr
  have hm : fr.maps = true := by
    show (Scc.Lower.X64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  exact ⟨hm, fnCodeC2 hm (hgap_ofPlaceOK h i) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i)
    (Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2) hbo hbp⟩

/-- **Each compiled block's function's code from `PlaceOK`** on an
`Accepted2` program, at the layout `RuntimeLayout.ofPlaceOK h i` (any
immediates `i`), as `fnPh2_ofPlaceOK` numbers them: the `j`th compiled block
`d` with its lowering data `w` is the function `f = func2 (user d.name)
(paramsR d w.na) w.sc w.hp w.r`, whose frame `frOf ir f` records stack maps
(`maps`), whose entry block is at `CodeC2` from some label counter `n` and
whose later blocks are at `BlocksCodeC2`, at every return address of the
phase of `raL`. With `fnPh2_ofPlaceOK`'s other facts, use
`fnCodeC2_of_fnPh2` at its witnesses. -/
theorem fnCodeC2_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    let Ly := RuntimeLayout.ofPlaceOK h i
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        let f := func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r
        let fr := frOf ir f
        LowC2 p cfg.layout.obj d w ∧ fr.maps = true ∧
        ∃ n : Nat, ∀ ra' : Int64,
          Spike.Lib.X64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat →
          CodeC2 fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') n
              (Ly.lab (labelOf fr.fn "entry")) w.r.insts w.r.term ∧
            BlocksCodeC2 fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC2 o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') Ly.lab
              w.r.blocks := by
  intro o ir Ly
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h i
  refine ⟨ws, rt, hws, hir, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, n, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbo, hbp, -⟩ := H j d w hd hw
  have H' := fun ra' hra => fnCodeC2_of_fnPh2 h i hir hL hbo (hbp ra' hra)
  exact ⟨hL, (H' (Ly.lab raL) rfl).1, n, fun ra' hra => (H' ra' hra).2⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnPh2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnPh2_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.fnCodeC2_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCodeC2_ofPlaceOK

end Spike.Lib.LowerX64
