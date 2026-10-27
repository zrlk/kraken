/-
**Every compiled block's code facts from the placement check** (AArch64):
`FnCode2` (`Spike/Lib/LowerA64/ProgC2.lean`) for each compiled block of an
`Accepted2` program whose output passes `placeOKAt`, at the runtime layout
`RuntimeLayout.ofPlaceOK h (imms2Of p)`, the code predicate `CdCLE` and the
call predicate `BlC2L` at every return address of the phase of the one
after `scc_rt_main`'s `bl`, the walk predicate `TailAt2 p j`. The `Accepted2`
twin of `Spike/Lib/LowerA64/FnCodeOf.lean`.

- `inRun_block`, `inRun_entry`: a checked block's (the entry's) label has a
  cell at offset 0;
- `fnCode2_ofPlaceOKR`: the code facts at the lowering data `ws` (with its
  lowering context `lcx2`, parameter's word count, closed form, frame
  `ctxOf`'s, call predicate, the overflow block's facts, the prologue's
  `ProPh` at `c.ps` and the entry label with a cell), from `fnPh2_ofPlaceOK` (frame, prologue, spills,
  phases), `fnCodeC2LB` with `codeC2_cdCLE` (code) and `walk2_srcA`,
  `walk2Facts_ofAccepted2` (the walks' facts);
- `fnCode2_ofPlaceOK`: at every compiled block, with its lowering context
  and call predicate;
- `fnCode2Of`, `fnCode2Of_spec`: a choice of them, `fnSpecC2_allI`'s
  `hcode` at `compiled2 p`, its lowering contexts' externs the frontend's
  (`hord_ofAccepted2`'s `hext`).
-/
import Spike.Lib.LowerA64.FnCodeLE
import Spike.Lib.LowerA64.BlocksC1Code
import Spike.Lib.LowerA64.ProEdge2Of
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf hasAddChk)
open Scc.Cert.Rt.A64 (labelGap)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.LowerShape (func2 paramsR env2)
open Spike.Lib.LowerNode (Pairwise2 Low2 LowC2 compiled2 funcs2 lowerAll_accepted2_a64 TailAt2 tailAt2_of
  lcx2 lits2 walk2_srcA walk2Facts_ofAccepted2 compiled2_facts fresh_env2)

/-- **A checked block's label has a cell at offset 0** (`InRun`): the code
of a block of `BlockC2` at a context with maps begins with an instruction
(`insts2_head`, `term2_head`), and the placement's block check (`blocksOk`)
puts it at the block's label. -/
theorem inRun_block {prog : List Directive} {cx : FnCtx} (hm : cx.maps = true) {b : Scc.IR.Block}
    (hs : Spike.Lib.LowerShape.BlockC2 b) {k : Nat} {l : Label} {code : List Item}
    (hc : Scc.Cert.Code1A64.blockItems cx k b = .ok code)
    (hseg : Scc.Cert.Code1A64.segIn prog l (directives code) = true) : Scc.Cert.Rt.A64.InRun prog l 0 := by
  cases hi : Scc.Cert.Code1A64.instsItems cx k b.insts with
  | error e => simp [Scc.Cert.Code1A64.blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      exact inRun0_of_segIn (zs := []) (by simpa using hseg)
        (insts2_head hm (term2_head hs.2 ht) _ _ _ hs.1 hi)

/-- **A checked function's entry label has a cell at offset 0** (`InRun`,
`inRun_block` at the entry block). -/
theorem inRun_entry {prog : List Directive} {cx : FnCtx} (hm : cx.maps = true)
    {r : Spike.Lib.LowerShape.Res2} (hs : Spike.Lib.LowerShape.ResC2 r) {name : Scc.IR.Sym}
    {ps sc hq : List Scc.IR.Reg} {entry : Label} (hent : cx.blockLabel "entry" = .ok entry)
    (hok : Scc.Cert.Code1A64.blocksOk prog cx 0 (func2 name ps sc hq r).blocks = true) :
    Scc.Cert.Rt.A64.InRun prog entry 0 := by
  obtain ⟨l, code, hl, hc, hseg⟩ := Scc.Cert.Code1A64.blocksOk_block (pre := [])
    (b := ⟨"entry", r.insts, r.term⟩) (post := r.blocks) hok
  rw [hent] at hl; cases hl
  exact inRun_block hm ⟨hs.1, hs.2.1⟩ hc hseg

/-- **Every compiled block's code facts from the placement check, at the
lowering data**: for an `Accepted2` program `p` whose output passes
`placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h (imms2Of p)`,
there are lowering data `ws` (`lowerAll`'s IR the runtime's 18 functions
`rt` then `funcs2 p ws`) such that the `j`th compiled block `d`, with
lowering data `w`, has `FnCode2` at the code predicate `CdCLE` of every
return address of the phase of `bareMC.e0 + 4`, the immediates `imms2Of p`
and the walk predicate `TailAt2 p j`, with the lowering context `lcx2`, the
parameter's word count `w.na`, the closed form `w.r`, the frame `ctxOf ir
(rt.length + j) (func2 (user d.name) (paramsR d w.na) w.sc w.hp w.r)`, the
call predicate `BlC2L`, with a checked `+` the overflow block's code and
phase facts, the prologue's phase facts (`ProPh`) at its spills, and the
body's entry label with a cell at offset 0 (`inRun_entry`), off the write
abort's labels. -/
theorem fnCode2_ofPlaceOKR {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let raM := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (ws : List Low2) (rt : List Scc.IR.Func),
      Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws) ∧ rt.length = 18 ∧
      ∀ (j : Nat) (d : Decl) (w : Low2), (compiled2 p)[j]? = some d → ws[j]? = some w →
        ∃ c : FnCode2 Ly.exe Ly.prog Ly.endPc
          (fun ra => Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
            Spike.Lib.A64.PhRec.ph Ly raM.toBitVec.toNat)
          (fun ra => CdCLE o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
            (Int64.ofBitVec ra))
          (Scc.Lower.imms2Of p) (TailAt2 p j) d,
          c.lcx = lcx2 p cfg.layout.obj d ∧ c.na = w.na ∧ c.r = w.r ∧
          c.cx = ctxOf ir (rt.length + j) (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r) ∧
          c.Bl = (fun ra => BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab c.cx
            (Int64.ofBitVec ra)) ∧
          (hasAddChk (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r) = true →
            Scc.Cert.Rt.A64.blockAt o.prog (c.cx.local "abort_overflow") 0 ovfBlk = true ∧
            Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (fun _ => false)
              Ly.lab (Ly.lab (c.cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 A64.Abort.Local.lb = true) ∧
          ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
            (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps ∧
          Scc.Cert.Rt.A64.InRun o.prog c.entry 0 ∧ c.entry ∉ Spike.Lib.A64.AllocG.abLabs := by
  intro o Ly ir raM
  obtain ⟨ws, rt, hws, hir, -, H⟩ := fnPh2_ofPlaceOK hp h (Scc.Lower.imms2Of p)
  have hrt : rt.length = 18 := by
    obtain ⟨_, hlow⟩ := lowerAll?_ok_of_placeOK2 h
    obtain ⟨ws', rt', hws', hrt', -, hir', -⟩ := lowerAll_accepted2_a64 cfg hp hlow
    have e := congrArg (fun q => q.funcs.length) (hir.symm.trans hir')
    simp only [Scc.Lower.Inv.progOf, List.length_append, funcs2, List.length_zipWith, hws.1, hws'.1,
      Nat.min_self] at e
    rw [← rtFuncs_length hrt']
    omega
  refine ⟨ws, rt, hws, hir, hrt, fun j d w hd hw => ?_⟩
  obtain ⟨hL, -, hfo, hle, h16, entry, ps, hent, hsp, hpro, hbo, hbp, hphP, hovf⟩ := H j d w hd hw
  have hfi : (ctxOf ir (rt.length + j)
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).fi ≠ 9 ∧
      (ctxOf ir (rt.length + j)
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).fi ≠ 12 ∧
      (ctxOf ir (rt.length + j)
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).fi ≠ 16 := by
    have e : (ctxOf ir (rt.length + j)
        (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).fi = rt.length + j := rfl
    omega
  have hm : (ctxOf ir (rt.length + j)
      (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)).maps = true := by
    show (Scc.Lower.A64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := Spike.Lib.A64.Rt.rS0 Ly)
  have hgap : ∀ a b n, labelGap o.prog a b n = true → Ly.lab b = Ly.lab a + Int64.ofNat (4 * n) :=
    fun _ _ _ hg => by rw [← hI.labOk]; exact Scc.Cert.Rt.A64.label_labelGap hI.lays hg
  have hs := Spike.Lib.LowerShape.lowerC2_resC2 _ _ _ _ _ _ _ hL.2.2
  have hcd := fun (ra' : Int64) hra =>
    let hc := fnCodeC2LB hm hgap (lab_ofPlaceOK h _) hfi ⟨_, rfl⟩ hs hent hbo (hbp ra' hra)
    And.intro (codeC2_cdCLE (fun _ _ _ h => BlC2L.posOff h) hs.2.1 _ _ _ hc.1).1
      (blocksCodeC2_cdCLE (fun _ _ _ h => BlC2L.posOff h) (fun b hb => (hs.2.2 b hb).2) hc.2)
  have hdc : d ∈ compiled2 p := List.mem_of_getElem? hd
  obtain ⟨hWk, hcnt, hxchg⟩ := walk2_srcA hp hdc hL
  have hF := walk2Facts_ofAccepted2 (obj := cfg.layout.obj) hp hdc hL.1
  exact ⟨{
    lcx := lcx2 p cfg.layout.obj d
    Bl := fun ra => BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
      (ctxOf ir (rt.length + j) (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r))
      (Int64.ofBitVec ra)
    cx := ctxOf ir (rt.length + j) (func2 (Scc.Lower.Names.user d.name) (paramsR d w.na) w.sc w.hp w.r)
    fn := Scc.Lower.Names.user d.name
    entry
    kp := Ly.pfx
    env := env2 d w.na
    r := w.r
    ps
    lits := lits2 d
    hf := hfo
    h1 := hle
    h16
    hp := Ly.lays
    hend := rfl
    hfn := rfl
    hpro := hpro
    hps := (paramSpillN_of_spills hfo hle h16 hsp).hps hle
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
    hsp := hsp }, rfl, rfl, rfl, rfl, rfl, hovf, hphP, inRun_entry hm hs hent hbo,
    blockLabel_not_abLabs hfi hent⟩

/-- **Every compiled block's code facts from the placement check**: for an
`Accepted2` program `p` whose output passes `placeOKAt`, at the runtime
layout `RuntimeLayout.ofPlaceOK h (imms2Of p)`, the `j`th compiled block has
`FnCode2` at the code predicate `CdCLE` of every return address of the
phase of `bareMC.e0 + 4`, the immediates `imms2Of p` and the walk predicate
`TailAt2 p j`, with the lowering context `lcx2` and the call predicate
`BlC2L`. -/
theorem fnCode2_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
    let raM := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d →
      ∃ c : FnCode2 Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.A64.PhRec.ph Ly raM.toBitVec.toNat)
        (fun ra => CdCLE o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
          (Int64.ofBitVec ra))
        (Scc.Lower.imms2Of p) (TailAt2 p j) d,
        c.lcx = lcx2 p cfg.layout.obj d ∧
        c.Bl = fun ra => BlC2L o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab c.cx
          (Int64.ofBitVec ra) := by
  intro o Ly raM j d hd
  obtain ⟨ws, rt, hws, -, -, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, h1, -, -, -, h5, -⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  exact ⟨c, h1, h5⟩

/-- **A choice of every compiled block's code facts** from the placement
check (`fnCode2_ofPlaceOK`): `fnSpecC2_allI`'s `hcode` at `compiled2 p`. -/
noncomputable def fnCode2Of {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    FnCode2 (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).exe (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).prog
      (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).endPc
      (fun ra => Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p))
          (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p))
          (Int64.ofBitVec ((RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab bareMC.e0 + 4).toBitVec
            ).toBitVec.toNat)
      (fun ra => CdCLE (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
        (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
        (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
        (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (Int64.ofBitVec ra))
      (Scc.Lower.imms2Of p) (TailAt2 p j) d :=
  Classical.choose (fnCode2_ofPlaceOK hp h j d hd)

/-- **`fnCode2Of`'s lowering context and call predicate**: `lcx2` (so its
externs are the frontend's, `hord_ofAccepted2`'s `hext`) and `BlC2L`. -/
theorem fnCode2Of_spec {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    (fnCode2Of hp h j d hd).lcx = lcx2 p cfg.layout.obj d ∧
    (fnCode2Of hp h j d hd).lcx.externs = Scc.Frontend.externs p ∧
    (fnCode2Of hp h j d hd).Bl = fun ra => BlC2L (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (Spike.Lib.A64.PhRec.okPc (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
      (Spike.Lib.A64.PhRec.ph (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)))
      (RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)).lab (fnCode2Of hp h j d hd).cx (Int64.ofBitVec ra) := by
  have hs := Classical.choose_spec (fnCode2_ofPlaceOK hp h j d hd)
  refine ⟨hs.1, ?_, hs.2⟩
  show (Classical.choose (fnCode2_ofPlaceOK hp h j d hd)).lcx.externs = _
  rw [hs.1]

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.fnCode2_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnCode2_ofPlaceOKR

/-- info: 'Spike.Lib.LowerA64.fnCode2Of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnCode2Of_spec

/-- info: 'Spike.Lib.LowerA64.inRun_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.inRun_block

/-- info: 'Spike.Lib.LowerA64.inRun_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.inRun_entry
