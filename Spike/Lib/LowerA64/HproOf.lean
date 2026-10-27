/-
**`CalleePre2.hpro` from `PlaceOK`** (AArch64; the twin of
`Spike/Lib/LowerX64/HproOf.lean`): for an `Accepted2` program whose output
passes `placeOKAt`, the prologue inputs of `hpro_setup` / `hpro_main`
(`Spike/Lib/LowerA64/ProW2.lean`) that the placement check gives, so a
caller supplies only the walk's: the record's instance (`instOk_ofPlaceOK`),
the runtime's code (`printIn`, `abortIn`), the prologue's phase facts and
its function index off the write abort's labels (`fnCode2_ofPlaceOKR`), and
the abort phase over the prologue (`proW_abStC`). The placement check does
not check the overflow stub's block (`proL`): its position off the write
abort is a premise (`hL`). The body's entry label is a position off the
write abort since its code begins with an instruction (`inRun_entry`, in
`ProOK`).

- `ProOK`: a compiled block's function index off the write abort's local
  labels, its prologue's phase facts at a runtime layout, and its entry
  label's position off the write abort;
- `fnCode2_ofPlaceOKP` / `fnCode2OfP` / `fnCode2OfP_spec`: every compiled
  block's code facts with `ProOK` (`fnCode2_ofPlaceOK` with it);
- `fnCode2_ofPlaceOKP2` / `fnCode2OfP_spec2`: the same with the lowering
  data `w` (`LowC2`), the parameter's word count `c.na = w.na` and the
  context `c.cx = ctxOf ir fi f` at the IR function `f` at index `fi`
  (`fnCode2OfP` chooses from it);
- `hpro_setup_ofPlaceOK`, `hpro_main_ofPlaceOK`: `hpro_setup` / `hpro_main`
  at the record of an output passing `placeOKAt`, the abort phase's part
  `proW_abStC`.
-/
import Spike.Lib.LowerA64.ProW2
import Spike.Lib.LowerA64.FnCode2Build

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedS InvS)
open Spike.Lib.A64.Rt (RuntimeLayout argX bareMC)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 lcx2)

/-- **A compiled block's prologue facts** at a runtime layout `Ly`: its
function index none of the runtime's whose local labels the write abort
reads (`local_not_abLabs`), its prologue's phase facts at `Ly`'s record,
and its entry label a position off the write abort. -/
def ProOK (Ly : RuntimeLayout) {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) : Prop :=
  (c.cx.fi ≠ 9 ∧ c.cx.fi ≠ 12 ∧ c.cx.fi ≠ 16) ∧
    ProPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab (c.cx.local "stack_check")
      (Int64.ofInt c.cx.frame) (proL c.cx) c.ps ∧
    PosOff prog Ly.lab (Ly.lab c.entry)

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

include hp in
/-- **Every compiled block's code facts with its prologue's** from the
placement check (`fnCode2_ofPlaceOKR`): `fnCode2_ofPlaceOK`'s, and
`ProOK` (the function index `18 + j`). -/
theorem fnCode2_ofPlaceOKP :
    ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d →
      ∃ c : FnCode2 (LY).exe (LY).prog (LY).endPc
        (fun ra => Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat)
        (fun ra => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
          (Int64.ofBitVec ra))
        (Scc.Lower.imms2Of p) (TailAt2 p j) d,
        c.lcx = lcx2 p cfg.layout.obj d ∧
        c.Bl = (fun ra => BlC2L OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab c.cx
          (Int64.ofBitVec ra)) ∧
        ProOK LY c := by
  intro j d hd
  obtain ⟨ws, rt, hws, -, hrt, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, h1, -, -, hcx, h5, -, hph, hin, hab⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  refine ⟨c, h1, h5, ?_, hph, c.entry, 0, hin, hab, by rw [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero]⟩
  rw [hcx]
  show rt.length + j ≠ 9 ∧ rt.length + j ≠ 12 ∧ rt.length + j ≠ 16
  omega

include hp in
/-- **`fnCode2_ofPlaceOKP` with the lowering data and the context**
(`fnCode2_ofPlaceOKR`): `fnCode2_ofPlaceOKP`'s facts, and lowering data `w`
of `d` (`LowC2`) with the parameter's word count `c.na = w.na`, the IR
function `func2 …` at index `fi` of the lowered IR, and the context
`c.cx = ctxOf ir fi (func2 …)`. -/
theorem fnCode2_ofPlaceOKP2 :
    ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d →
      ∃ c : FnCode2 (LY).exe (LY).prog (LY).endPc
        (fun ra => Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat)
        (fun ra => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
          (Int64.ofBitVec ra))
        (Scc.Lower.imms2Of p) (TailAt2 p j) d,
        (c.lcx = lcx2 p cfg.layout.obj d ∧
          c.Bl = (fun ra => BlC2L OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab c.cx
            (Int64.ofBitVec ra)) ∧
          ProOK LY c) ∧
        ∃ (w : Spike.Lib.LowerNode.Low2) (fi : Nat), Spike.Lib.LowerNode.LowC2 p cfg.layout.obj d w ∧
          c.na = w.na ∧
          (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
            w.hp w.r, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx ∧
          c.cx = Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi
            (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
              w.hp w.r) := by
  intro j d hd
  obtain ⟨ws, rt, hws, hir, hrt, H⟩ := fnCode2_ofPlaceOKR hp h
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  have hjw : j < ws.length := hws.1 ▸ hj
  obtain ⟨c, h1, hna, -, hcx, h5, -, hph, hin, hab⟩ := H j _ ws[j] hd (List.getElem?_eq_getElem hjw)
  refine ⟨c, ⟨h1, h5, ?_, hph, c.entry, 0, hin, hab, by rw [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero]⟩,
    ws[j], rt.length + j, hws.get j hj, hna, ?_, hcx⟩
  · rw [hcx]
    show rt.length + j ≠ 9 ∧ rt.length + j ≠ 12 ∧ rt.length + j ≠ 16
    omega
  · show _ ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx
    rw [hir]
    exact Spike.Lib.LowerNode.mem_progOf_funcs2 cfg.layout rt hws j hj

/-- **A choice of every compiled block's code facts with its prologue's**
(`fnCode2_ofPlaceOKP2`). -/
noncomputable def fnCode2OfP (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.A64.PhRec.ph LY (Int64.ofBitVec ((LY).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      (Scc.Lower.imms2Of p) (TailAt2 p j) d :=
  Classical.choose (fnCode2_ofPlaceOKP2 hp h j d hd)

/-- **`fnCode2OfP`'s lowering context, call predicate and prologue facts.** -/
theorem fnCode2OfP_spec (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    (fnCode2OfP hp h j d hd).lcx = lcx2 p cfg.layout.obj d ∧
    (fnCode2OfP hp h j d hd).Bl = (fun ra => BlC2L OP (Spike.Lib.A64.PhRec.okPc LY)
      (Spike.Lib.A64.PhRec.ph LY) (LY).lab (fnCode2OfP hp h j d hd).cx (Int64.ofBitVec ra)) ∧
    ProOK LY (fnCode2OfP hp h j d hd) :=
  (Classical.choose_spec (fnCode2_ofPlaceOKP2 hp h j d hd)).1

/-- **`fnCode2OfP`'s lowering data, parameter count and context**
(`fnCode2_ofPlaceOKP2`). -/
theorem fnCode2OfP_spec2 (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    ∃ (w : Spike.Lib.LowerNode.Low2) (fi : Nat), Spike.Lib.LowerNode.LowC2 p cfg.layout.obj d w ∧
      (fnCode2OfP hp h j d hd).na = w.na ∧
      (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
        w.hp w.r, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx ∧
      (fnCode2OfP hp h j d hd).cx = Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi
        (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
          w.hp w.r) :=
  (Classical.choose_spec (fnCode2_ofPlaceOKP2 hp h j d hd)).2

variable {im : Expr → String → Nat → Option Nat}
variable {d : Decl} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {T : Expr → Prop} {rS : Range} {Λw : Scc.Sem.Layout} {lbl : Lbl} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lsize : Lsize}

/-- **The setup function's prologue inside `W2` from the placement check**
(`hpro_setup` at the record of an output passing `placeOKAt`): the
instance `instOk_ofPlaceOK`, the prologue's facts `ProOK` (`hc`, e.g.
`fnCode2OfP_spec`), the abort phase over the prologue by `proW_abStC` at
the write abort, and the overflow stub's position off the write abort
(`hL`); the walk's inputs as `hpro_setup`'s. -/
theorem hpro_setup_ofPlaceOK (c : FnCode2 (LY).exe (LY).prog (LY).endPc RaOk Cd im T d)
    (hc : ProOK LY c) (hL : PosOff OP (LY).lab ((LY).lab (proL c.cx))) {ms : MemSide isaLSE2}
    {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.A64.Flow.Ret0.WcG}
    {c0 : Ctl} {fr : TermRun.Frame}
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λw) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hpN : ProgNoS ZBad p)
    (hct : CallTo p c0 g.c0 fr) (hcE : g.c0 = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hW0 : ∀ x ty ws, TermRun.lookupE c0.env x = some (ty, ws) → ws = []) (hfo : FrOk2 g.c0 [fr]) :
    ProW (fun s c => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
        (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c [fr])
      (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc R F ms
      ((_root_.Executable.labels (LY).exe).label c.fn) (Int64.ofInt c.cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps
      (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels (LY).exe).label ms0 F0 (LY).exe (LY).endPc fn ZU g).J := by
  obtain ⟨hfi, hph, hent⟩ := hc
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  exact hpro_setup c hI hph hR hal hlo hhi hl hh hmr hun hsub hfit hFO hpN
    (proW_abStC c hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfi hL hent
      (fun _ _ h => h.1.2.2.2.2) hR hal hlo hhi hun) hct hcE hW0 hfo

/-- **`main`'s prologue inside `W2` from the placement check**
(`hpro_main` at the record of an output passing `placeOKAt`): as
`hpro_setup_ofPlaceOK`; the walk's inputs as `hpro_main`'s. -/
theorem hpro_main_ofPlaceOK (c : FnCode2 (LY).exe (LY).prog (LY).endPc RaOk Cd im T d)
    (hc : ProOK LY c) (hL : PosOff OP (LY).lab ((LY).lab (proL c.cx))) {ms : MemSide isaLSE2}
    {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.A64.Flow.Ret0.WcG}
    {Pre : Ctl → Reg64s → Prop} {JE : AS → Ctl → Prop}
    (hJE : ∀ σ c, JE σ c →
      (Spike.Lib.A64.Rt.uNM (_root_.Executable.labels (LY).exe).label ms0 F0 (LY).exe (LY).endPc fn ZU Pre g).J σ c)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λw) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hpN : ProgNoS ZBad p)
    (hPl : ∀ c (regs : Reg64s), Pre c regs → ∀ s : State,
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = regs.getXReg (argX i)) → PlacedS Λw lbl s c [])
    (hnr : ∀ c regs, Pre c regs → ∀ a, c.term ≠ .ret a) (hfo : ∀ c regs, Pre c regs → FrOk2 c []) :
    ProW (fun s c => W2 Λw (Spike.Lib.A64.PhRec.μ LY) p rd G (Spike.Lib.A64.PhRec.own LY) rS
        (Spike.Lib.A64.PhRec.Tk LY) ar J Dt (A64.WriteAb.Ab (LY).lab) lbl lsize s c [])
      (Spike.Lib.A64.PhRec.K LY rS) (LY).exe (LY).endPc R F ms
      ((_root_.Executable.labels (LY).exe).label c.fn) (Int64.ofInt c.cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.cx) c.ps JE := by
  obtain ⟨hfi, hph, hent⟩ := hc
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  exact hpro_main c hI hJE hph hR hal hlo hhi hl hh hmr hun hsub hfit hFO hpN
    (proW_abStC c hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfi hL hent
      (fun σ c h => (hJE σ c h).1.2.2.2.2) hR hal hlo hhi hun) hPl hnr hfo

end Place

/-- info: 'Spike.Lib.LowerA64.fnCode2_ofPlaceOKP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnCode2_ofPlaceOKP

/-- info: 'Spike.Lib.LowerA64.fnCode2OfP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnCode2OfP_spec

/-- info: 'Spike.Lib.LowerA64.fnCode2_ofPlaceOKP2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnCode2_ofPlaceOKP2

/-- info: 'Spike.Lib.LowerA64.fnCode2OfP_spec2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnCode2OfP_spec2

/-- info: 'Spike.Lib.LowerA64.hpro_setup_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hpro_setup_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.hpro_main_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hpro_main_ofPlaceOK

end Spike.Lib.LowerA64
