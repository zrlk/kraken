/-
**A landing context's resumption at the extended placement** (AArch64):
the allocating frame's `ResumeCx2T` (`Spike/Lib/LowerA64/ResumeCx2T.lean`)
at a landing context `CxOkH` with its bottom key `BotH`, at the extended
placement `upd L l b`, `updN ls l n` of a placement reachable from none, at
any walk restriction `Tr`, for any `Accepted2` program with a setup block.
The aborts' fragment is `AbG2L` at the extended placement (the base
contexts' aborts there), which holds the context's abort node since the
context is a base context there (`cxCore2L_ofCxOkH`).

- the code's program by `fnCode2OfPMe_spec`; the region's facts and the
  ghosts' closure from `CxCore2L`;
- the body's and pending blocks by `cxBlk2_ofCxOkHA` at the extended
  placement (the frames `[fr]` discharge the `main`-return premise);
- the abort node at `TailAt2 p j ∧ Tr j` inside `AbG2L`
  (`at_abortN2_monoT`);
- the plain calls, lane stores, buffers and output calls by
  `callLU_ofCxOkH` at `TailAt2 p j`, restricted to `Tr j` (`monoTA`).

- `resumeLU_ofCxOkH`: the resumption.
-/
import Spike.Lib.LowerA64.G1CallLU
import Spike.Lib.LowerA64.G1H1Mono
import Spike.Lib.LowerA64.ResumeCx2T
import Spike.Test.A64Hello1ResL

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section ResLU

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
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
walk restriction `Tr`, at the base contexts' aborts `AbG2L` there: the
region's facts from `cxCore2L_ofCxOkH` (the allocations' `W2` instance by
`allocW2AtL_ofCxOkH`), the blocks by `cxBlk2_ofCxOkHA`, the abort node
inside `AbG2L` (`at_abortN2_monoT`), the constructs by `callLU_ofCxOkH`
restricted to `Tr j`. -/
theorem resumeLU_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (htg : tgOkB OP = true)
    (E : Entry) {J : InvS} (hJ : ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
        Spike.Lib.A64.Rt.rtF (Ly) m) (ElH h hp) (fun _ => True) (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs)
    (Tr : Nat → Expr → Prop) {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hre : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hC : CxOkH h hp j R F fs fp ra tp G0 Ab) (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs)
    (hra : Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph (LY0)
        (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat) :
    ResumeCx2T (W2T J (LU) (LN)) (KT) p (LU) (LN) (MSR J (LU) (LN)) (FC) R F fs fp ra tp G0
      (AbG2L h hp (fun _ => True) J (LU) (LN)) (Tr j) := by
  have hre' := Reach.step hre hl hAL
  have hAW := allocW2AtL_ofCxOkH h hp hty hobj E hJ hre' hd hC hB (T := TailAt2 p j) fun _ h' => h'
  have hcore := cxCore2L_ofCxOkH h hp hty hcfg J hre' hd hC hB hAW
  obtain ⟨hcall, hlane, hbuf, hpc, -⟩ := callLU_ofCxOkH h hp hty hcfg htg J hre' hd hC hB hAW hra
  have hblk := cxBlk2_ofCxOkHA h hp hty htg (Dt := fun _ => True) J (LU) (LN) hd hC
  have hfs : fs ≠ [] := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := hC
    exact List.cons_ne_nil _ _
  have hT : ∀ t, (TailAt2 p j t ∧ Tr j t) → TailAt2 p j t := fun _ h' => h'.1
  have hA : ∀ s c fs', AbG2L h hp (fun _ => True) J (LU) (LN) s c fs' →
      AbG2L h hp (fun _ => True) J (LU) (LN) s c fs' := fun _ _ _ h' => h'
  exact ⟨by rw [(fnCode2OfPMe_spec hp h Λ j d hd).1], hcore.hFS, hcore.hR, hcore.hal, hcore.hhi, hcore.hG0,
    fun s c => (W2T J (LU) (LN)) s c fs, fun _ _ h' => h',
    fun c0 hc0 pc t s lits cs bufs blk hsub hk => hblk.1 c0 hc0 pc t s lits cs bufs blk hsub hk (absurd · hfs),
    fun c0 hc0 pc t s lits cs bufs k blk hsub hk h1 =>
      hblk.2 c0 hc0 pc t s lits cs bufs k blk hsub hk h1 (absurd · hfs),
    fun c0 hc0 s c' hA' => ⟨j, d, hd, R, F, fs, fp, ra, tp, G0, hcore, .inl ⟨rfl, c0, hc0, at_abortN2_monoT hT hA'⟩⟩,
    hcall.monoTA hT hA, hlane.monoTA hT hA, hbuf.monoTA hT hA, hpc.monoTA hT hA⟩

end ResLU

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.resumeLU_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resumeLU_ofCxOkH
