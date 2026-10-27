/-
**Every code block's code facts from the placement check** (AArch64, H7a
calls), the twin of `Spike/Lib/LowerX64/FnCodeOf.lean`: `FnCode`
(`Spike/Lib/LowerA64/ProgC.lean`) for each code block of an `Accepted1`
program lowered and passing `placeOKAt`, at the runtime layout
`RuntimeLayout.ofPlaceOK h (imms1Of p)`, the code predicates `CdC`/`BlC` at
every return address of the phase of the one after `scc_rt_main`'s `bl`,
the walk predicate `InWalkD`/`InWalkC`.

- `fnCode_ofPlaceOKR`, `fnCode_ofPlaceOKX`, `fnCode_ofPlaceOK`: the code
  facts (the first at the closed forms, with its closed form, frame
  `ctxOf`'s, parameter registers, block predicate, the overflow block's
  facts and the prologue's `ProPh` at `c.ps`; the first two with its
  context's program, no frames limit, entry environment and counter), from
  `fnPh1_ofPlaceOK` (frame, prologue, spills, phases), `fnCodeC_of_fnPh1`
  (code), `immIn_imms1OfC` (immediates) and `walkC_retOne` (returns).

Where AArch64 differs from x86-64: the frame is the emitter's context
`ctxOf ir (rt.length + j) f` (indexed), the return addresses are those of
the phase of `bareMC.e0 + 4`, and `FnCode` has no depth limit field (`frm`)
and no prologue label offsets (`zl`, …): the prologue's phases are
`ProPh` at its label `stack_check`.
-/
import Spike.Lib.LowerA64.ProgC
import Spike.Lib.LowerA64.BlocksC1Code
import Spike.Lib.LowerA64.CallSite1
import Spike.Lib.LowerEnvImmC1Of

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf hasAddChk)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Scc.Lower.Inv (Res1 func1 params1R env1)
open Spike.Lib.LowerNode (Pairwise2 LowC lowerEnvsC Fresh)

/-- **Every code block's code facts from the placement check, at the
closed forms**: for an `Accepted1` program `p` lowered to `em` and an output
passing `placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h
(imms1Of p)`, there are closed forms `rs` (`lowerAll`'s IR the runtime
functions `rt` then `funcs1 p rs`) such that the `j`th code block, with
closed form `r`, has `FnCode` at the code predicate `CdC` of every return
address of the phase of `bareMC.e0 + 4`, the immediates `imms1Of p` and the
walk predicate `InWalkD` of its own walk (with no frames limit), with its
context's program and no frames limit (plain calls), its entry environment and
counter, its closed form `r`, its parameter registers `params1R d`, its
frame `ctxOf ir (rt.length + j) (func1 (user d.name) (params1R d) r)`, its
block predicate `BlC`, with a checked `+` the overflow block's code and
phase facts, and the prologue's phase facts (`ProPh`) at its spills. -/
theorem fnCode_ofPlaceOKR {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let raM := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∃ (rs : List Res1) (rt : List Scc.IR.Func),
      Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs1 p rs) ∧
      ∀ (j : Nat) (d : Decl), p[j]? = some d → ∃ (r : Res1) (c : FnCode Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.A64.PhRec.ph Ly raM.toBitVec.toNat)
        (fun ra => CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab (Int64.ofBitVec ra))
        (Scc.Lower.imms1Of p) (InWalkD none d) d),
        rs[j]? = some r ∧ c.lcx.prog = p ∧ c.lcx.frames = none ∧
        c.env = env1 d ∧ c.n = 0 ∧ c.r = r ∧ c.prs = params1R d ∧
        c.cx = ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user d.name) (params1R d) r) ∧
        c.Bl = (fun ra => BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab c.cx
          (Int64.ofBitVec ra)) ∧
        (hasAddChk (func1 (Scc.Lower.Names.user d.name) (params1R d) r) = true →
          Scc.Cert.Rt.A64.blockAt o.prog (c.cx.local "abort_overflow") 0 ovfBlk = true ∧
          Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (fun _ => false)
            Ly.lab (Ly.lab (c.cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 A64.Abort.Local.lb = true) ∧
        ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
          (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps := by
  intro o Ly ir raM
  obtain ⟨rs, rt, hrs, hir, -, H⟩ := fnPh1_ofPlaceOK hp hlow h (Scc.Lower.imms1Of p)
  refine ⟨rs, rt, hrs, hir, fun j d hd => ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  have hjr : j < rs.length := hrs.1 ▸ hj
  have hr : rs[j]? = some rs[j] := List.getElem?_eq_getElem hjr
  obtain ⟨hL, -, hfo, hle, h16, entry, ps, hent, hsp, hpro, hbo, hbp, hphP, hovf⟩ := H j p[j] rs[j] hd hr
  have hcd := fun (ra' : Int64) hra => fnCodeC_of_fnPh1 hp h (Scc.Lower.imms1Of p) hir hd hL hent hbo (hbp ra' hra)
  -- the code block's acceptance
  have hp' := hp
  simp only [Scc.Lower.Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hd1 := Spike.Lib.LowerCallOrder.decl1_of_decls1 hp'.1.2 hd
  simp only [Scc.Lower.decl1, Bool.and_eq_true, beq_iff_eq] at hd1
  have harg : p[j].argTy = .unit ∨ p[j].argTy = .int := by
    have := hd1.1.2
    split at this
    · exact .inl (by simpa using this)
    · exact .inr (by simpa using this)
  have hmem : p[j] ∈ p := List.getElem_mem hj
  exact ⟨rs[j], {
    lcx := { prog := p, externs := [], fn := p[j].name, obj := cfg.layout.obj,
             frames := none }
    Bl := fun ra => BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab
      (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j]))
      (Int64.ofBitVec ra)
    cx := ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j])
    fn := Scc.Lower.Names.user p[j].name
    entry
    kp := Ly.pfx
    env := env1 p[j]
    n := 0
    l := "entry"
    k := 0
    r := rs[j]
    kk := 0
    ps
    prs := params1R p[j]
    hf := hfo
    h1 := hle
    h16
    hp := Ly.lays
    hend := rfl
    hfn := rfl
    hpro := hpro
    hsp := paramSpill_of_spills hfo hle h16 hsp
    hr := hL
    hfr := fresh_env1 _
    hCd := fun ra _ => cdOf_cdC Ly.lays rfl
    hcode := fun ra hra => (hcd (Int64.ofBitVec ra) hra).2.1
    hbl := fun ra hra => (hcd (Int64.ofBitVec ra) hra).2.2
    hImm := fun q hq => ⟨Spike.Lib.LowerNode.immIn_imms1OfC hp hmem _ q hq, q, hq, rfl⟩
    hOne := fun q hq a ha =>
      Spike.Lib.LowerCallOrder.walkC_retOne _ _ _ _ _ hd1.2 (Scc.Lower.Inv.envScalar_env1 harg) q hq a ha },
    hr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hovf, hphP⟩

/-- **Every code block's code facts from the placement check**: for an
`Accepted1` program `p` lowered to `em` and an output passing `placeOKAt`,
at the runtime layout `RuntimeLayout.ofPlaceOK h (imms1Of p)`, the `j`th
code block has `FnCode` at the code predicate `CdC` of every return address
of the phase of `bareMC.e0 + 4`, the immediates `imms1Of p` and the walk
predicate `InWalkD` (with no frames limit). -/
theorem fnCode_ofPlaceOKX {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)
    let raM := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∀ (j : Nat) (d : Decl), p[j]? = some d →
      ∃ c : FnCode Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.A64.PhRec.ph Ly raM.toBitVec.toNat)
        (fun ra => CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab (Int64.ofBitVec ra))
        (Scc.Lower.imms1Of p) (InWalkD none d) d,
        c.lcx.prog = p ∧ c.env = env1 d ∧ c.n = 0 ∧
        c.Bl = fun ra => BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab c.cx
          (Int64.ofBitVec ra) := by
  intro o Ly raM j d hd
  obtain ⟨rs, rt, -, -, H⟩ := fnCode_ofPlaceOKR hp hlow h
  obtain ⟨-, c, -, h1, -, h3, h4, -, -, -, h5, -⟩ := H j d hd
  exact ⟨c, h1, h3, h4, h5⟩

/-- **Every code block's code facts from the placement check**
(`fnCode_ofPlaceOKX` without the facts on its fields, at the walk
predicate `InWalkC` of every code block). -/
theorem fnCode_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    let o := Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)
    let raM := Int64.ofBitVec (Ly.lab bareMC.e0 + 4).toBitVec
    ∀ (j : Nat) (d : Decl), p[j]? = some d →
      Nonempty (FnCode Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.A64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.A64.PhRec.ph Ly raM.toBitVec.toNat)
        (fun ra => CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab (Int64.ofBitVec ra))
        (Scc.Lower.imms1Of p) (InWalkC p none) d) :=
  fun j d hd =>
    let ⟨c, _⟩ := fnCode_ofPlaceOKX hp hlow h j d hd
    ⟨c.monoT fun _ => InWalkD.inWalkC (List.mem_of_getElem? hd)⟩

end Spike.Lib.LowerA64
