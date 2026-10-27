/-
**Every code block's code facts from the placement check** (x86-64, H7a
calls): `FnCode` for each code block of an `Accepted1` program lowered and
passing `placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h
(imms1Of p)`, the code predicates `CdC`/`BlC` at every return address of
the phase of `raL`, the walk predicate `InWalkC`.

- `InWalkC`: a term at a point of some code block's walk with calls;
  `InWalkD`: of a given code block's walk.
- `fresh_env1`: a code block's entry environment is fresh from `0` (its
  parameter register `x.0` is no `fresh` name).
- `fnCode_ofPlaceOKR`, `fnCode_ofPlaceOKX`, `fnCode_ofPlaceOK`: the code
  facts (the first at the closed forms, with its closed form, frame and the
  overflow block's facts; the first two with its context's program, depth
  limit, entry environment, counter and block predicate), from `fnPh1_ofPlaceOK` (frame,
  prologue and spills), `fnCodeC_ofPlaceOK` (code), `immIn_imms1OfC`
  (immediates) and `walkC_retOne` (returns).
-/
import Spike.Lib.LowerX64.ProgC
import Spike.Lib.LowerX64.BlocksC1Code
import Spike.Lib.LowerX64.CallSite1
import Spike.Lib.SlotOrderC1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Lower.Inv (Res1 func1 params1R env1)
open Spike.Lib.LowerNode (Pairwise2 LowC lowerEnvsC Fresh)

/-- **A term at a point of some code block's walk with calls** (from its
entry environment, at the depth limit `frames`). -/
def InWalkC (p : Prog) (frames : Option Nat) (e : Expr) : Prop :=
  ∃ d ∈ p, ∃ q ∈ lowerEnvsC frames (env1 d) 0 d.body, q.1 = e

/-- **A term at a point of the code block `d`'s walk with calls** (from its
entry environment, at the depth limit `frames`). -/
def InWalkD (frames : Option Nat) (d : Decl) (e : Expr) : Prop :=
  ∃ q ∈ lowerEnvsC frames (env1 d) 0 d.body, q.1 = e

/-- A point of a code block's walk is a point of some code block's walk. -/
theorem InWalkD.inWalkC {p : Prog} {frames : Option Nat} {d : Decl} (hd : d ∈ p) {e : Expr}
    (h : InWalkD frames d e) : InWalkC p frames e :=
  let ⟨q, hq, he⟩ := h; ⟨d, hd, q, hq, he⟩

/-- **A code block's entry environment is fresh from `0`**: its parameter
register `x.0` is no `fresh` name (`param_ne_regName`). -/
theorem fresh_env1 (d : Decl) : Fresh (env1 d) 0 := by
  intro v hv o ho r hr y k _
  simp only [env1, List.mem_singleton] at hv
  subst hv
  simp only [params1R] at ho
  split at ho
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
    subst ho
    cases hr
    exact Spike.Lib.SlotOrder.param_ne_regName d.arg y k
  · cases ho

/-- **Every code block's code facts from the placement check, at the
closed forms**: for an `Accepted1` program `p` lowered to `em` and an output
passing `placeOKAt`, at the runtime layout `RuntimeLayout.ofPlaceOK h
(imms1Of p)`, there are closed forms `rs` (`lowerAll`'s IR the runtime
functions `rt` then `funcs1 p rs`) such that the `j`th code block, with
closed form `r`, has `FnCode` at the code predicate `CdC` of every return
address of the phase of `raL`, the immediates `imms1Of p` and the walk
predicate `InWalkD` of its own walk (no depth limit: plain calls), with
its context's program and no depth limit, its entry environment and counter,
its closed form `r`, its parameter registers `params1R d`, its frame that of `func1 (user d.name) (params1R d) r`,
its block predicate `BlC`, and with a checked `+` the overflow block's code
and phase facts, and the prologue's phase facts (`ProPh`). -/
theorem fnCode_ofPlaceOKR {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    ∃ (rs : List Res1) (rt : List Scc.IR.Func),
      Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs1 p rs) ∧
      ∀ (j : Nat) (d : Decl), p[j]? = some d → ∃ (r : Res1) (c : FnCode Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.X64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat)
        (fun ra => CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab (Int64.ofBitVec ra))
        (Scc.Lower.imms1Of p) (InWalkD none d) d),
        rs[j]? = some r ∧ c.lcx.prog = p ∧ c.lcx.frames = none ∧
        c.env = env1 d ∧ c.n = 0 ∧ c.r = r ∧ c.prs = params1R d ∧
        c.fr = frOf ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r) ∧
        c.Bl = (fun ra => BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fr
          (Int64.ofBitVec ra)) ∧
        (Scc.Cert.Code1X64.hasAddChk (func1 (Scc.Lower.Names.user d.name) (params1R d) r) = true →
          Scc.Cert.Rt.X64.blockAtB o.prog (ovfL c.fr) 0 ovfBlk = true ∧
          Spike.Lib.X64Consumer.blkPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) (fun _ => false) Ly.lab
            (Ly.lab (ovfL c.fr) + Int64.ofNat 0) 0 Spike.Lib.X64.Abort.Local.lb = true) ∧
        ProPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fn
          (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps := by
  intro o Ly ir
  obtain ⟨rs, rt, hrs, hir, -, H⟩ := fnPh1_ofPlaceOK hp hlow h (Scc.Lower.imms1Of p)
  obtain ⟨rs', rt', hrs', -, H'⟩ := fnCodeC_ofPlaceOK hp hlow h (Scc.Lower.imms1Of p)
  refine ⟨rs, rt, hrs, hir, fun j d hd => ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  have hjr : j < rs.length := hrs.1 ▸ hj
  have hjr' : j < rs'.length := hrs'.1 ▸ hj
  have hL := hrs.get j hj
  have hL' := hrs'.get j hj
  have hrr : rs'[j] = rs[j] := Option.some.inj (hL'.symm.trans hL)
  obtain ⟨-, -, n, zl, zf, z1, z2, zs, zps, ps, -, hfo, hlt, -, -, hsp, hpro, -, -, hphP, hovf⟩ :=
    H j p[j] rs[j] hd (List.getElem?_eq_getElem hjr)
  obtain ⟨-, -, kk, hcd⟩ := H' j p[j] rs'[j] hd (List.getElem?_eq_getElem hjr')
  rw [hrr] at hcd
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
    Bl := fun ra => BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j]))
      (Int64.ofBitVec ra)
    fr := frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j])
    fn := Scc.Lower.Names.user p[j].name
    entry := Scc.Emit.X64.labelOf (Scc.Lower.Names.user p[j].name) "entry"
    zl, zf, z1, z2, zs
    kp := Ly.pfx
    env := env1 p[j]
    n := 0
    l := "entry"
    k := 0
    r := rs[j]
    kk
    ps
    prs := params1R p[j]
    hf := hfo
    h1 := by omega
    hp := Ly.lays
    hend := rfl
    hfn := rfl
    hpro := hpro
    hps := hps_of_spills hfo (by omega) hsp
    hr := hL
    hfr := fresh_env1 _
    hCd := fun ra _ => cdOf_cdC Ly.lays rfl
    hcode := fun ra hra => (hcd (Int64.ofBitVec ra) hra).1
    hbl := fun ra hra => (hcd (Int64.ofBitVec ra) hra).2
    hImm := fun q hq => ⟨Spike.Lib.LowerNode.immIn_imms1OfC hp hmem _ q hq, q, hq, rfl⟩
    hOne := fun q hq a ha =>
      Spike.Lib.LowerCallOrder.walkC_retOne _ _ _ _ _ hd1.2 (Scc.Lower.Inv.envScalar_env1 harg) q hq a ha },
    List.getElem?_eq_getElem hjr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hovf, hphP⟩

/-- **Every code block's code facts from the placement check**: for an
`Accepted1` program `p` lowered to `em` and an output passing `placeOKAt`,
at the runtime layout `RuntimeLayout.ofPlaceOK h (imms1Of p)`, the `j`th
code block has `FnCode` at the code predicate `CdC` of every return address
of the phase of `raL`, the immediates `imms1Of p` and the walk predicate
`InWalkC` (no depth limit: plain calls). -/
theorem fnCode_ofPlaceOKX {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)
    ∀ (j : Nat) (d : Decl), p[j]? = some d →
      ∃ c : FnCode Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.X64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat)
        (fun ra => CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab (Int64.ofBitVec ra))
        (Scc.Lower.imms1Of p) (InWalkD none d) d,
        c.lcx.prog = p ∧ c.lcx.frames = none ∧ c.env = env1 d ∧ c.n = 0 ∧
        c.Bl = fun ra => BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fr
          (Int64.ofBitVec ra) := by
  intro o Ly j d hd
  obtain ⟨rs, rt, -, -, H⟩ := fnCode_ofPlaceOKR hp hlow h
  obtain ⟨-, c, -, h1, h2, h3, h4, -, -, -, h5, -, -⟩ := H j d hd
  exact ⟨c, h1, h2, h3, h4, h5⟩

/-- **Every code block's code facts from the placement check**
(`fnCode_ofPlaceOKX` without the facts on its fields). -/
theorem fnCode_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    let o := Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)
    ∀ (j : Nat) (d : Decl), p[j]? = some d →
      Nonempty (FnCode Ly.exe Ly.prog Ly.endPc
        (fun ra => Spike.Lib.X64.PhRec.ph Ly (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat)
        (fun ra => CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab (Int64.ofBitVec ra))
        (Scc.Lower.imms1Of p) (InWalkC p none) d) :=
  fun j d hd =>
    let ⟨c, _⟩ := fnCode_ofPlaceOKX hp hlow h j d hd
    ⟨c.monoT fun _ => InWalkD.inWalkC (List.mem_of_getElem? hd)⟩

end Spike.Lib.LowerX64
