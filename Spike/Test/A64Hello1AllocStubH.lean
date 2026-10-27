/-
**`AllocPtW.hstub` at `OpenAPtA`'s instance** (AArch64): the allocator's
heap abort path's obligations without code inside `W2` at the record, at
every landing context `CxOkH` and allocation placed by its resumption facts
(`PtC2`), at the write tail `fun _ => True`: `hstub_ofNbJc`
(`Spike/Test/A64Hello1AllocStub.lean`) at the call node `nbJc … nbJ1`
(`nbJcOf_nbJ1` from `PtC2.newBufW`), in the setup callee region `CxOkH`
gives (its `PRE` and bounds, as `cxLB_hAW_noneA`), the frame `[fr]` placed
at no label (`framesPlaced_setup`).

- `hello1_hstubA`: `AllocPtW.hstub`'s conclusion at `OpenAPtA`'s
  `AllocPtW` arguments at `Dt := fun _ => True`.
-/
import Spike.Test.A64Hello1HAWNone
import Spike.Test.A64Hello1AllocStub

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Flow.NewBuf (nbJc)
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.LowerNode (setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.AllocReach (Reach IN)
open Scc.Emit.A64 (directives)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)
set_option hygiene false in
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
set_option hygiene false in
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
set_option hygiene false in
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs
set_option hygiene false in
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m
set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd
set_option hygiene false in
/-- **`AllocPtW`'s memory side at `OpenAPtA`'s instance** over `IN … J`. -/
local notation "MSA" J:max => msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
  (Spike.Lib.A64.PhRec.GOf Ly M0) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (arOf (Ly).Λ)
  (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) (fun _ => none) (fun _ => 0) fs
set_option hygiene false in
/-- **The allocation's call node** after the argument moves `la`
(`AllocPtW.hstub`'s at `OpenAPtA`'s instance). -/
local notation "NJA" la:max => nbJc (_root_.Executable.labels (Ly).exe).label
  [blD Scc.Lower.Names.alloc] (pc + Int64.ofNat (4 * (directives la).length)) (oF (FC).cx)
  (nbJ1 p (fun _ => none) (fun _ => 0) (FC).cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs
    (Scc.Lower.imm hh) (.imm kv) (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))

/-- **`AllocPtW.hstub` at `OpenAPtA`'s instance**: at a landing context
`CxOkH` of the `rodata` block (`hd`, `hc`) and an allocation
`let x = newBuf cn τ in e` of an `elem2` element type (`hel`) placed by its
resumption facts (`hpt`), the allocator's heap abort path's obligations
without code inside `W2` at the record (`hstub_ofNbJc` at the call node
`nbJcOf_nbJ1`, in the setup callee region, the frame `[fr]` placed, the
write tail `fun _ => True`). -/
theorem hello1_hstubA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab') {J : InvS}
    {c0 : Ctl} {pc : Int64} {kk : Nat} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {kv : UInt64} {en em hh : Nat}
    (hel : Scc.Lower.elem2 τ = true)
    (hpt : PtC2 (FC).lcx (FC).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
      (BlC2L OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (FC).cx
        (Int64.ofBitVec ra))
      (_root_.Executable.labels (Ly).exe).label (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) kk pc env n lits
      cs bufs (.let_ x (.newBuf cn τ) e)) :
    ∀ la : List Scc.Emit.A64.Item, (FC).cx.getArgs [Scc.Lower.imm hh, .imm kv,
        Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv] = .ok la →
      ∀ q : Call, q.OK (MSA J) (_root_.Executable.labels (Ly).exe).label →
        ∀ J' : InvS, (∀ L ls, Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls → ∀ s c fs,
          StartsN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) (S0A h E (WNF)) El L ls s c fs →
            J' L ls s c fs) →
        ∀ m0 σC c0', (HeldAb (_root_.Executable.labels (Ly).exe).label (MSA J') q (fun _ => none) R
          (FC).cx.frame (fun σC => (NJA la) σC q.c0)).J σC c0' →
        StubHN (fun s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
            (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly))
            (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J')
            (fun _ => True) (Ab (LY0).lab) (fun _ => none) (fun _ => 0) s c fs)
          (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (MSA J') (Ly).exe (Ly).endPc
          (R.callee (-((FC).cx.frame : Int) + -160) (-48) 0)
          (fun m => F m ∧ CKept R (-((FC).cx.frame : Int) + -160) (-48) 0 m0 m ∧
            Abs R ⟨-((FC).cx.frame : Int) + -160, []⟩ m0 σC) c0' := by
  intro la _ q hq J' _
  obtain ⟨d', hd', L', D1', fS', nS', v', g, fr, J'', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, -, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).cx.frame = fS' := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hFO : ∀ m, F m → StackOff (rS0 (Ly))
      ((swR v' (-L') 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1') 0) m := by
    intro m hm
    obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).base.toNat % 8 = 0 := by
      show (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L') % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L' ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hq' := callOK_msOfAX (I' := IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J') hq
  have hJc := nbJcOf_nbJ1 (p := p) (lbl := fun _ => none) (lsize := fun _ => 0) (cx := (FC).cx)
    (fp := g.fp) (ra := g.ra) (tp := UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))
    (c0 := c0) (lits := lits) (cs := cs) (bufs := bufs) (a0 := Scc.Lower.imm hh)
    (a1 := .imm kv) (a2 := Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)
    (_root_.Executable.labels (Ly).exe).label (pc + Int64.ofNat (4 * (directives la).length)) hel
    (PtC2.newBufW hpt).1 (PtC2.newBufW hpt).2.1 (PtC2.newBufW hpt).2.2.1
  exact hstub_ofNbJc h (imms2Me Λ p) (FC).hf (FC).h16 hR0 hal
    (by
      show -D1' ≤ _
      simp only [Spike.Lib.A64.Flow.NewBuf.allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]
      rw [hframe]; omega)
    (by show (0 : Int) ≤ 0; exact Int.le_refl _) (by show (-D1') % 8 = 0; omega)
    (by show (0 : Int) % 8 = 0; rfl) hF' (Spike.Lib.A64.Rt.rS0_sub _)
    (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO
    (fun s _ => framesPlaced_setup h hp hty hct s) (fun _ _ _ _ _ _ => trivial) hJc q hq'

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_hstubA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hstubA
