/-
**A landing context's resumption at the extended placement** (x86-64; the
twin of `Spike/Lib/LowerA64/G1H1Res.lean`): the allocating frame's
`ResumeCx2T` (`Spike/Lib/LowerX64/ResumeCx2T.lean`) at a landing context
`CxOkH` with its bottom key `BotH`, at the extended placement `upd L l b`,
`updN ls l n` of a placement reachable from none, at any walk restriction
`Tr`, for any `Accepted2` program with a setup block. The aborts' fragment
is `AbG2L` at the extended placement (the base contexts' aborts there),
which holds the context's abort node since the context is a base context
there at its region `rbR R` (`cxCore2L_ofCxOkH`, the frame condition met
by the abort node's state).

- the parts independent of the constructs by `resumeLU_ofParts`;
- the abort node at `TailAt2 p j ∧ Tr j` inside `AbG2L`
  (`at_abortN2_monoT`);
- the plain calls, lane stores, buffers and output calls by
  `callLU_ofCxOkH` at `TailAt2 p j`, restricted to `Tr j` (`monoTA`); the
  allocations' `W2` instance by `allocW2AtL_ofCxOkH`.

- `resumeLU_ofCxOkH`: the resumption.
-/
import Spike.Lib.LowerX64.G1CallLU
import Spike.Lib.LowerX64.G1AllocL
import Spike.Lib.LowerX64.G1H1Mono
import Spike.Lib.LowerX64.G1H1ResB

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (rS0 rtF)
open Spike.Lib.LowerNode (compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section ResLU

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The start's frame condition: the private memory loading no runtime word and `rtF`. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

/-- **A landing context's `ResumeCx2T` at the extended placement** at any
walk restriction `Tr`, at the base contexts' aborts `AbG2L` there: by
`resumeLU_ofParts`, the abort node inside `AbG2L` (the context a base
context at `rbR R` by `cxCore2L_ofCxOkH`, the frame condition from the
node's state, `at_F`; `at_abortN2_monoT`), the constructs by
`callLU_ofCxOkH` restricted to `Tr j` (the allocations' `W2` instance by
`allocW2AtL_ofCxOkH`). -/
theorem resumeLU_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (htg : tgOkB OP = true)
    (E : Entry) {J : InvS} (hJ : ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElG h hp) (fun _ => True) (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs)
    (Tr : Nat → Expr → Prop) {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hre : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hC : CxOkH h hp j R F fs fp ra tp G0 Ab) (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs)
    (hra : Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat) :
    ResumeCx2T (W2T J (LU) (LN)) (KT) p (LU) (LN) (MSR J (LU) (LN)) (FC) R F fs fp ra tp G0
      (AbG2L h hp (fun _ => True) J (LU) (LN)) (Tr j) := by
  have hre' := Reach.step hre hl hAL
  have hAW := allocW2AtL_ofCxOkH h hp hty hobj E hJ hre' hd hC hB (T := TailAt2 p j) fun _ h' => h'
  obtain ⟨hcall, hlane, hbuf, hpc, -⟩ := callLU_ofCxOkH h hp hty hcfg htg J hre' hd hC hB hAW hra
  have hT : ∀ t, (TailAt2 p j t ∧ Tr j t) → TailAt2 p j t := fun _ h' => h'.1
  have hA : ∀ s c fs', AbG2L h hp (fun _ => True) J (LU) (LN) s c fs' →
      AbG2L h hp (fun _ => True) J (LU) (LN) s c fs' := fun _ _ _ h' => h'
  exact resumeLU_ofParts h hp hty htg J (Tr j) hre hl hAL hd hC
    (fun c0 hc0 s c' hA' => ⟨j, d, hd, rbR R, F, fs, fp, ra, tp, G0,
      cxCore2L_ofCxOkH h hp hty hcfg J hre' hd hC hB ⟨_, at_F hA'⟩ hAW,
      .inl ⟨rfl, c0, hc0, at_abortN2_monoT hT hA'⟩⟩)
    ⟨hcall.monoTA hT hA, hlane.monoTA hT hA, hbuf.monoTA hT hA, hpc.monoTA hT hA⟩

end ResLU

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.resumeLU_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.resumeLU_ofCxOkH
