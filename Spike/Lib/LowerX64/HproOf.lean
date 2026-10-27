/-
**`CalleePre2.hpro` from `PlaceOK`** (x86-64; the twin of
`Spike/Lib/LowerA64/HproOf.lean`): for an `Accepted2` program whose output
passes `placeOKAt`, the prologue inputs of `hpro_setup` / `hpro_main`
(`Spike/Lib/LowerX64/ProW2.lean`) that the placement check gives, so a
caller supplies only the walk's: the record's instance (`instOk_ofPlaceOK`),
the runtime's code (`printIn`, `abortIn`), the prologue's phase facts and
labels (`fnCode2_ofPlaceOKR`), and the abort phase over the prologue
(`proW_abStC`). The placement check does not check the overflow stub's
block (`labelOf fn "stk"`, `proL`): its position off the write abort is a
premise (`hL`). The body's entry label has a cell since its code begins
with an instruction (`inRunB_entry`, in `ProOK`).

- `ProOK`: a compiled block's frame function, entry label, prologue
  phase facts at a runtime layout, and the entry label's cell;
- `fnCode2_ofPlaceOKP` / `fnCode2OfP` / `fnCode2OfP_spec`: every compiled
  block's code facts with `ProOK` (`fnCode2_ofPlaceOK` with it);
- `fnCode2_ofPlaceOKP2` / `fnCode2OfP_spec2`: the same with the lowering
  data `w` (`LowC2`), the parameter's word count `c.na = w.na` and the
  frame `c.fr = frOf ir f` at the IR function `f` of the lowered IR
  (`fnCode2OfP` chooses from it);
- `posOff_labelOf_user`: a user function's label with a cell is a position
  off the write abort;
- `hpro_setup_ofPlaceOK`, `hpro_main_ofPlaceOK`: `hpro_setup` / `hpro_main`
  at the record of an output passing `placeOKAt`, the abort phase's part
  `proW_abStC`.
-/
import Spike.Lib.LowerX64.ProW2
import Spike.Lib.LowerX64.FnCode2Build

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Emit.X64 (labelOf)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW CallTo)
open Spike.Lib.X64Consumer (K0 Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedS InvS)
open Spike.Lib.X64ConsumerA (AbSt)
open Spike.Lib.X64.Rt (RuntimeLayout argXs)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 lcx2)
open Scc.Cert.Rt.X64 (InRunB)

/-- **A compiled block's prologue facts** at a runtime layout `Ly`: its
frame's function `user d.name`, its entry label `labelOf (user d.name)
"entry"`, its prologue's phase facts at `Ly`'s record, and its entry label
with a cell at offset 0. -/
def ProOK (Ly : RuntimeLayout) (d : Decl) {exe : _root_.Executable} {cells : List (Directive × Nat)}
    {endPc : Int64} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (c : FnCode2 exe cells endPc RaOk Cd i T d) :
    Prop :=
  c.fr.fn = Scc.Lower.Names.user d.name ∧ c.entry = labelOf (Scc.Lower.Names.user d.name) "entry" ∧
    ProPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab c.fn (labelOf c.fr.fn "chk")
      (Int64.ofInt c.fr.size) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps ∧
    InRunB cells c.entry 0

/-- **A user function's label with a cell at offset 0 is a position off the
write abort.** -/
theorem posOff_labelOf_user {cells : List (Directive × Nat)} {lab : Label → Int64} {f : String} {l : String}
    (h : InRunB cells (labelOf (Scc.Lower.Names.user f) l) 0) :
    PosOff cells lab (lab (labelOf (Scc.Lower.Names.user f) l)) :=
  ⟨_, 0, h, labelOf_user_not_abLabs _ _, by rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]⟩

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

include hp in
/-- **Every compiled block's code facts with its prologue's** from the
placement check (`fnCode2_ofPlaceOKR`): `fnCode2_ofPlaceOK`'s, and
`ProOK`. -/
theorem fnCode2_ofPlaceOKP :
    ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d →
      ∃ c : FnCode2 (LY).exe (LY).prog (LY).endPc
        (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
        (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
          (Int64.ofBitVec ra))
        (Scc.Lower.imms2Of p) (TailAt2 p j) d,
        c.lcx = lcx2 p cfg.layout.obj d ∧
        c.Bl = (fun ra => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab c.fr
          (Int64.ofBitVec ra)) ∧
        ProOK LY d c := by
  intro j d hd
  obtain ⟨ws, rt, hws, -, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, h1, -, -, hfr, h5, -, hph, hen, hin⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  exact ⟨c, h1, h5, by rw [hfr]; rfl, hen, hph, hin⟩

include hp in
/-- **`fnCode2_ofPlaceOKP` with the lowering data and the frame**
(`fnCode2_ofPlaceOKR`): `fnCode2_ofPlaceOKP`'s facts, and lowering data `w`
of `d` (`LowC2`) with the parameter's word count `c.na = w.na`, the IR
function `func2 …` among the lowered IR's, and the frame
`c.fr = frOf ir (func2 …)`. -/
theorem fnCode2_ofPlaceOKP2 :
    ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d →
      ∃ c : FnCode2 (LY).exe (LY).prog (LY).endPc
        (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
          Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
        (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
          (Int64.ofBitVec ra))
        (Scc.Lower.imms2Of p) (TailAt2 p j) d,
        (c.lcx = lcx2 p cfg.layout.obj d ∧
          c.Bl = (fun ra => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab c.fr
            (Int64.ofBitVec ra)) ∧
          ProOK LY d c) ∧
        ∃ w : Spike.Lib.LowerNode.Low2, Spike.Lib.LowerNode.LowC2 p cfg.layout.obj d w ∧ c.na = w.na ∧
          Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
            w.hp w.r ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs ∧
          c.fr = frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
            (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
              w.hp w.r) := by
  intro j d hd
  obtain ⟨ws, rt, hws, hir, H⟩ := fnCode2_ofPlaceOKR hp h
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  have hjw : j < ws.length := hws.1 ▸ hj
  obtain ⟨c, h1, hna, -, hfr, h5, -, hph, hen, hin⟩ := H j _ ws[j] hd (List.getElem?_eq_getElem hjw)
  refine ⟨c, ⟨h1, h5, by rw [hfr]; rfl, hen, hph, hin⟩, ws[j], hws.get j hj, hna, ?_, hfr⟩
  have hmem := Spike.Lib.LowerNode.mem_progOf_funcs2 cfg.layout rt hws j hj
  rw [← hir, List.mem_zipIdx_iff_getElem?] at hmem
  exact List.mem_of_getElem? hmem

/-- **A choice of every compiled block's code facts with its prologue's**
(`fnCode2_ofPlaceOKP2`). -/
noncomputable def fnCode2OfP (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      (Scc.Lower.imms2Of p) (TailAt2 p j) d :=
  Classical.choose (fnCode2_ofPlaceOKP2 hp h j d hd)

/-- **`fnCode2OfP`'s lowering context, call predicate and prologue facts.** -/
theorem fnCode2OfP_spec (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    (fnCode2OfP hp h j d hd).lcx = lcx2 p cfg.layout.obj d ∧
    (fnCode2OfP hp h j d hd).Bl = (fun ra => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY)
      (Spike.Lib.X64.PhRec.ph LY) (LY).lab (fnCode2OfP hp h j d hd).fr (Int64.ofBitVec ra)) ∧
    ProOK LY d (fnCode2OfP hp h j d hd) :=
  (Classical.choose_spec (fnCode2_ofPlaceOKP2 hp h j d hd)).1

/-- **`fnCode2OfP`'s lowering data, parameter count and frame**
(`fnCode2_ofPlaceOKP2`). -/
theorem fnCode2OfP_spec2 (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    ∃ w : Spike.Lib.LowerNode.Low2, Spike.Lib.LowerNode.LowC2 p cfg.layout.obj d w ∧
      (fnCode2OfP hp h j d hd).na = w.na ∧
      Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
        w.hp w.r ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs ∧
      (fnCode2OfP hp h j d hd).fr = frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
          w.hp w.r) :=
  (Classical.choose_spec (fnCode2_ofPlaceOKP2 hp h j d hd)).2

variable {im : Expr → String → Nat → Option Nat}
variable {d : Decl} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {T : Expr → Prop} {rS : Range} {Λw : Scc.Sem.Layout} {lbl : Lbl} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lsize : Lsize}

/-- **The setup function's prologue inside `W2` from the placement check**
(`hpro_setup` at the record of an output passing `placeOKAt`): the
instance `instOk_ofPlaceOK`, the prologue's facts `ProOK` (`hc`, e.g.
`fnCode2OfP_spec`), the abort phase over the prologue by `proW_abStC` at
the write abort, and the overflow stub's position off the write abort
(`hL`); the walk's inputs as `hpro_setup`'s. -/
theorem hpro_setup_ofPlaceOK (c : FnCode2 (LY).exe (LY).prog (LY).endPc RaOk Cd im T d)
    (hc : ProOK LY d c) (hL : PosOff OP (LY).lab ((LY).lab (proL c.fr))) {ms : MemSide isa}
    {ms0 : MemSide isa} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.X64.Flow.Ret0.WcG}
    {c0 : Ctl} {fr : TermRun.Frame}
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hpN : ProgNoS ZBad p)
    (hct : CallTo p c0 g.c0 fr) (hcE : g.c0 = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hW0 : ∀ x ty ws, TermRun.lookupE c0.env x = some (ty, ws) → ws = []) (hfo : FrOk2 g.c0 [fr]) :
    XProW (fun s c => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c [fr])
      (Spike.Lib.X64.PhRec.K LY rS) (LY).exe (LY).endPc R F ms
      ((_root_.Executable.labels (LY).exe).label c.fn) (Int64.ofInt c.fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps
      (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (LY).exe).label ms0 F0 fn ZU g).J := by
  obtain ⟨hfr, hen, hph, hent⟩ := hc
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  have hE : PosOff OP (LY).lab ((LY).lab c.entry) := hen ▸ posOff_labelOf_user (hen ▸ hent)
  exact hpro_setup c hI hph hR hR8 hlo hhi hl hh hmr hun hsub hfit hFO hpN
    (proW_abStC c hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfr hL hE
      (fun _ _ h => h.1.2.2.2.2) hR hlo hhi hun) hct hcE hW0 hfo

/-- **`main`'s prologue inside `W2` from the placement check**
(`hpro_main` at the record of an output passing `placeOKAt`): as
`hpro_setup_ofPlaceOK`; the walk's inputs as `hpro_main`'s. -/
theorem hpro_main_ofPlaceOK (c : FnCode2 (LY).exe (LY).prog (LY).endPc RaOk Cd im T d)
    (hc : ProOK LY d c) (hL : PosOff OP (LY).lab ((LY).lab (proL c.fr))) {ms : MemSide isa}
    {ms0 : MemSide isa} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.X64.Flow.Ret0.WcG}
    {Pre : Ctl → Reg64s → Prop} {JE : AS → Ctl → Prop}
    (hJE : ∀ σ c, JE σ c →
      (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (LY).exe).label ms0 F0 fn ZU Pre g).J σ c)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hpN : ProgNoS ZBad p)
    (hPl : ∀ c (regs : Reg64s), Pre c regs → ∀ s : State,
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = regs.get64 (argXs.getD i .rdi)) → PlacedS Λw lbl s c [])
    (hnr : ∀ c regs, Pre c regs → ∀ a, c.term ≠ .ret a) (hfo : ∀ c regs, Pre c regs → FrOk2 c []) :
    XProW (fun s c => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c [])
      (Spike.Lib.X64.PhRec.K LY rS) (LY).exe (LY).endPc R F ms
      ((_root_.Executable.labels (LY).exe).label c.fn) (Int64.ofInt c.fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE := by
  obtain ⟨hfr, hen, hph, hent⟩ := hc
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS)
  have hE : PosOff OP (LY).lab ((LY).lab c.entry) := hen ▸ posOff_labelOf_user (hen ▸ hent)
  exact hpro_main c hI hJE hph hR hR8 hlo hhi hl hh hmr hun hsub hfit hFO hpN
    (proW_abStC c hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hph hfr hL hE
      (fun σ c h => (hJE σ c h).1.2.2.2.2) hR hlo hhi hun) hPl hnr hfo

end Place

/-- info: 'Spike.Lib.LowerX64.posOff_labelOf_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_labelOf_user

/-- info: 'Spike.Lib.LowerX64.fnCode2_ofPlaceOKP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnCode2_ofPlaceOKP

/-- info: 'Spike.Lib.LowerX64.fnCode2OfP_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnCode2OfP_spec

/-- info: 'Spike.Lib.LowerX64.fnCode2_ofPlaceOKP2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnCode2_ofPlaceOKP2

/-- info: 'Spike.Lib.LowerX64.fnCode2OfP_spec2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnCode2OfP_spec2

/-- info: 'Spike.Lib.LowerX64.hpro_setup_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hpro_setup_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.hpro_main_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hpro_main_ofPlaceOK

end Spike.Lib.LowerX64
