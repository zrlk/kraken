/-
**Every compiled block's code facts from the placement check** (x86-64):
`FnCode2` (`Spike/Lib/LowerX64/ProgC2.lean`) for each compiled block of an
`Accepted2` program whose output passes `placeOKAt`, at the runtime layout
`RuntimeLayout.ofPlaceOK h (imms2Of p)`, the code predicate `CdCLE` and the
call predicate `BlC2L` at every return address of the phase of `raL`, the
walk predicate `TailAt2 p j`. The twin of
`Spike/Lib/LowerA64/FnCode2Build.lean`.

- `inRunB_entry`: a checked function's entry label has a cell at offset 0;
- `ParamSpillN.hps`: a `ParamSpillN`'s stores are cells of the frame
  (`FnCode2`'s `hps`);
- `fnCode2_ofPlaceOKR`: the code facts at the lowering data `ws` (with its
  lowering context `lcx2`, parameter's word count, closed form, frame
  `frOf`'s, call predicate, the overflow block's facts, the prologue's
  `ProPh` and the entry label with a cell), from `fnPh2_ofPlaceOK` (frame, prologue, spills, phases),
  `fnCodeC2LB_of_fnPh2` with `codeC2_cdCLE` (code) and `walk2_srcA`,
  `walk2Facts_ofAccepted2` (the walks' facts);
- `fnCode2_ofPlaceOK`: at every compiled block, with its lowering context
  and call predicate;
- `fnCode2Of`, `fnCode2Of_spec`: a choice of them, `fnSpecC2_allI`'s
  `hcode` at `compiled2 p`, its lowering contexts' externs the frontend's
  (`hord_ofAccepted2`'s `hext`).

Where x86-64 differs from AArch64: the frame is `frOf ir f` (not indexed),
the entry label `labelOf (user d.name) "entry"`, the body's code from the
block start `n` (`kk`), the prologue's sizes `zl` … `zs` and the spill's
`zps`.
-/
import Spike.Lib.LowerX64.FnCodeLE
import Spike.Lib.LowerX64.BlocksC1Code
import Spike.Lib.LowerX64.ProEdge2Of
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.Code1X64 (hasAddChk)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.LowerShape (func2 paramsR env2)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2 TailAt2 tailAt2_of
  lcx2 lits2 walk2_srcA walk2Facts_ofAccepted2 fresh_env2)

/-- **A `ParamSpillN`'s stores are cells of the frame** (`FnCode2`'s
`hps`), at a frame below `2 ^ 31` bytes. -/
theorem ParamSpillN.hps {fr : Scc.Emit.X64.Frame} (h1 : fr.size < 2 ^ 31) {ps : List (Reg64 × Int64 × Nat)}
    {prs : List Scc.IR.Reg} {zs : List Nat} (h : ParamSpillN fr ps prs zs) :
    ∀ q ∈ ps, offOk (-8 - (Int64.ofInt fr.size).toInt) 0 (-8 + q.2.1.toInt) = true := by
  have hF : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  rw [hF]
  intro q hq
  obtain ⟨_, _, -, -, -, hok⟩ := h.2.2.mem q hq
  exact hok

/-- **A checked function's entry label has a cell at offset 0**
(`InRunB`): the code of a closed form of `ResC2` at a frame with maps
begins with a non-label (`code2_head`), and the placement's block check
(`blocksOk`) puts it at the entry's label. -/
theorem inRunB_entry {cells : List (Directive × Nat)} {fr : Scc.Emit.X64.Frame} (hm : fr.maps = true)
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg} {n : Nat}
    (hok : Scc.Cert.Code1X64.blocksOk cells fr n ((func2 name ps sc hq r).blocks.zip
      (Scc.IR.StackMap.callMaps (func2 name ps sc hq r))) = true) :
    Scc.Cert.Rt.X64.InRunB cells (labelOf fr.fn "entry") 0 := by
  obtain ⟨G, hz, hG⟩ := zip_callMaps (func2 name ps sc hq r)
  rw [hz] at hok
  obtain ⟨code, n', hc, hseg⟩ := Scc.Cert.Code1X64.blocksOk_block (pre := [])
    (b := ⟨"entry", r.insts, r.term⟩) hok
  unfold Scc.Cert.Code1X64.blockItems at hc
  split at hc
  · next s heq =>
    cases hc
    have heq' := heq
    rw [blockCode_eq fr ⟨"entry", r.insts, r.term⟩] at heq'
    exact inRunB0_of_segIn (zs := []) (by simpa using hseg)
      (code2_head hm hs.2.1 r.insts (G ⟨"entry", r.insts, r.term⟩) _ s s.out.reverse hs.1
        (Nat.le_of_eq (hG ⟨"entry", r.insts, r.term⟩).symm) heq' (by simp))
  · cases hc

/-- **Every compiled block's code facts from the placement check, at the
lowering data**: for an `Accepted2` program `p` whose output passes
`placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h (imms2Of p)`,
there are lowering data `ws` (`lowerAll`'s IR the runtime functions `rt`
then `funcs2 p ws`) such that the `j`th compiled block `d`, with lowering
data `w`, has `FnCode2` at the code predicate `CdCLE` of every return
address of the phase of `raL`, the immediates `imms2Of p` and the walk
predicate `TailAt2 p j`, with the lowering context `lcx2`, the parameter's
word count `w.na`, the closed form `w.r`, the frame `frOf ir (func2 (user
d.name) (paramsR d w.na) w.sc w.hp w.r)`, the call predicate `BlC2L`, with
a checked `+` the overflow block's code and phase facts, the prologue's
phase facts (`ProPh`), and the body's entry label `labelOf (user d.name)
"entry"`, with a cell at offset 0 (`inRunB_entry`). -/
theorem fnCode2_ofPlaceOKR {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        ∃ c : FnCode2 Ly.exe Ly.prog Ly.endPc
          (fun ra => Spike.Lib.X64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
            Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat)
          (fun ra => CdCLE o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab
            (Int64.ofBitVec ra))
          (Scc.Lower.imms2Of p) (TailAt2 p j) d,
          c.lcx = lcx2 p cfg.layout.obj d ∧ c.na = w.na ∧ c.r = w.r ∧
          c.fr = frOf ir (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r) ∧
          c.Bl = (fun ra => BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fr
            (Int64.ofBitVec ra)) ∧
          (hasAddChk (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r) = true →
            Scc.Cert.Rt.X64.blockAtB o.prog (ovfL c.fr) 0 ovfBlk = true ∧
            Spike.Lib.X64Consumer.blkPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) (fun _ => false)
              Ly.lab (Ly.lab (ovfL c.fr) + Int64.ofNat 0) 0 Spike.Lib.X64.Abort.Local.lb = true) ∧
          ProPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fn
            (labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps ∧
          c.entry = labelOf (Scc.Lower.Names.user d.name) "entry" ∧
          Scc.Cert.Rt.X64.InRunB o.prog c.entry 0 := by
  intro o Ly ir
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h (Scc.Lower.imms2Of p)
  refine ⟨ws, rt, hws, hir, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, n, zl, zf, z1, z2, zs, zps, ps, -, hfo, hlt, h16, -, hsp, hpro, hbo, hbp, hphP, hovf⟩ :=
    H j d w hd hw
  have hs := Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2
  have hm : (frOf ir (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).maps = true := by
    show (Scc.Lower.X64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hfn : (frOf ir (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).fn =
      Scc.Lower.Names.user d.name := rfl
  have hin : Scc.Cert.Rt.X64.InRunB o.prog (labelOf (Scc.Lower.Names.user d.name) "entry") 0 := by
    rw [← hfn]; exact inRunB_entry hm hs hbo
  have hcd := fun (ra' : Int64) hra =>
    let hc := (fnCodeC2LB_of_fnPh2 h (Scc.Lower.imms2Of p) hir hL hbo (hbp ra' hra)).2
    And.intro (codeC2_cdCLE (fun _ _ _ _ h => BlC2L.posOff h) hs.2.1 _ _ _ hc.1).1
      (blocksCodeC2_cdCLE (fun _ _ _ _ h => BlC2L.posOff h) (fun b hb => (hs.2.2 b hb).2) hc.2)
  have hdc : d ∈ compiled2 p := List.mem_of_getElem? hd
  obtain ⟨hWk, hcnt, hxchg⟩ := walk2_srcA hp hdc hL
  have hF := walk2Facts_ofAccepted2 (obj := cfg.layout.obj) hp hdc hL.1
  exact ⟨{
    lcx := lcx2 p cfg.layout.obj d
    Bl := fun ra => BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab
      (frOf ir (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)) (Int64.ofBitVec ra)
    fr := frOf ir (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)
    fn := Scc.Lower.Names.user d.name
    entry := labelOf (Scc.Lower.Names.user d.name) "entry"
    zl, zf, z1, z2, zs
    kp := Ly.pfx
    env := env2 d w.na
    r := w.r
    kk := n
    ps
    lits := lits2 d
    hf := hfo
    h1 := Nat.le_of_lt hlt
    h16
    hp := Ly.lays
    hend := rfl
    hfn := rfl
    hpro := hpro
    hps := (paramSpillN_of_spills hfo (Nat.le_of_lt hlt) hsp).hps hlt
    hfrm := rfl
    hr := hL.2.2
    hfr := fresh_env2 d w.na
    hCd := fun _ _ pc blk hc => cdOf_cdC Ly.lays rfl pc blk hc.1.toCdC
    hcode := fun ra hra => (hcd (Int64.ofBitVec ra) hra).1
    hbl := fun ra hra => (hcd (Int64.ofBitVec ra) hra).2
    hWk := fun q hq =>
      let ⟨h1, h2, h3, h4, h5⟩ := hWk q hq
      ⟨h1, tailAt2_of hd h2, h3, h4, h5⟩
    hlit := hF.2.1
    hretL := hF.2.2
    hcallL := Spike.Lib.LowerNode.callLk_ofAccepted2 hp hdc
    hcnt := hcnt
    hxchg := hxchg
    na := w.na
    henv := rfl
    hlits := rfl
    hsp := ⟨zps, hsp⟩ }, rfl, rfl, rfl, rfl, rfl, hovf, hphP, rfl, hin⟩

/-- **Every compiled block's code facts from the placement check**: for an
`Accepted2` program `p` whose output passes `placeOKAt`, at the runtime
layout `RuntimeLayout.ofPlaceOK h (imms2Of p)`, the `j`th compiled block has
`FnCode2` at the code predicate `CdCLE` of every return address of the
phase of `raL`, the immediates `imms2Of p` and the walk predicate `TailAt2
p j`, with the lowering context `lcx2` and the call predicate `BlC2L`. -/
theorem fnCode2_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
    ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d →
      ∃ c : FnCode2 Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.X64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat)
        (fun ra => CdCLE o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab
          (Int64.ofBitVec ra))
        (Scc.Lower.imms2Of p) (TailAt2 p j) d,
        c.lcx = lcx2 p cfg.layout.obj d ∧
        c.Bl = fun ra => BlC2L o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fr
          (Int64.ofBitVec ra) := by
  intro o Ly j d hd
  obtain ⟨ws, rt, hws, -, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, h1, -, -, -, h5, -⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  exact ⟨c, h1, h5⟩

/-- **A choice of every compiled block's code facts** from the placement
check (`fnCode2_ofPlaceOK`): `fnSpecC2_allI`'s `hcode` at `compiled2 p`. -/
noncomputable def fnCode2Of {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    FnCode2 (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).exe (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).prog
      (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).endPc
      (fun ra => Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p))
          (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p))
          ((RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab raL).toBitVec.toNat)
      (fun ra => CdCLE (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
        (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
        (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
        (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (Int64.ofBitVec ra))
      (Scc.Lower.imms2Of p) (TailAt2 p j) d :=
  Classical.choose (fnCode2_ofPlaceOK hp h j d hd)

/-- **`fnCode2Of`'s lowering context and call predicate**: `lcx2` (so its
externs are the frontend's, `hord_ofAccepted2`'s `hext`) and `BlC2L`. -/
theorem fnCode2Of_spec {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    (fnCode2Of hp h j d hd).lcx = lcx2 p cfg.layout.obj d ∧
    (fnCode2Of hp h j d hd).lcx.externs = Scc.Frontend.externs p ∧
    (fnCode2Of hp h j d hd).Bl = fun ra => BlC2L (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
      (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
      (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (fnCode2Of hp h j d hd).fr (Int64.ofBitVec ra) := by
  have hs := Classical.choose_spec (fnCode2_ofPlaceOK hp h j d hd)
  refine ⟨hs.1, ?_, hs.2⟩
  show (Classical.choose (fnCode2_ofPlaceOK hp h j d hd)).lcx.externs = _
  rw [hs.1]

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnCode2_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnCode2_ofPlaceOKR

/-- info: 'Spike.Lib.LowerX64.fnCode2Of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnCode2Of_spec

/-- info: 'Spike.Lib.LowerX64.inRunB_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.inRunB_entry
