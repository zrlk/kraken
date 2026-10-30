/-
**`AllocW2`'s allocator field at `W₀ := W2`** (AArch64): for a call `q`
returning past the `bl` at an allocation of an `Accepted2` body (the call
node `nbJc` past `nbJ1`), every node of `scc_rt_alloc` inside `W2` in the
allocator's region `R.callee (-frame) (-160) 0` under `AllocW2`'s frame
condition (`F`, the caller's cells, the call's context `AllocCtx`):
`allocW2X` with

- the frame condition stable in the allocator's region
  (`fstable_allocCtx`) and the stack range off it (`stackOff_allocCtx`,
  `stackOff_callee`);
- the call's control free of `ZBad` (`frOk2_allocCtx`: the ghost's, after
  `nbJ1`'s local run, `FrOk2.run`);
- the controls and frames placed (`allocHP`, `slotRep_nbJ1`);
- the counter add's held landing in `PendA` (`pendA_of_selfN`) by its own
  segment `allocHeld_sg2` (`Spike/Lib/LowerA64/AllocHeldW2.lean`, not
  circular: it asks neither `PendA` nor the full `allocW2`) and
  `allocHeld_nr`.
-/
import Spike.Lib.LowerA64.AllocHeldW2
import Spike.Lib.LowerA64.AbortSeg2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun MemSide SegW SegWS Frag.at)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (BlkW NodeW At holdCtr DFrame FStable CKept Abs AS blD)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK CallerCells)
open Spike.Lib.A64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64.AllocG (allocPhOk allocAbOkR)
open Spike.Lib.AllocReach (Reach IN)
open Scc.Emit.A64 (FnCtx)
open Scc.Lower.InvA64 (FrameOk)

/-! ## The frame condition in the allocator's region -/

section Frame

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {L : Label → Int64}
  {Jc : AS → Ctl → Prop} {q : Call} {fr : Int}

/-- **`AllocW2`'s frame condition is stable in the allocator's region**
`R.callee (-fr) (-160) 0`: the caller's `F` (`FStable.callee`), and the
caller's cells outside the region (`CallerCells`, the call's `CKept`), which
no write inside the region touches (`Region.callee_sep`). -/
theorem fstable_allocCtx (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -fr + -160) (hkc : -fr < R.hi)
    (hk8 : fr % 8 = 0) :
    FStable (R.callee (-fr) (-160) 0)
      (fun m => F m ∧ CallerCells R (-fr) (-160) 0 m ∧ AllocCtx ms L R fr Jc q m) := by
  rintro m m' ⟨hFm, hcc, mC, σC, c, hA, hJ, hN, hK⟩ hd
  have hsep : ∀ k, R.Off k → ¬ (R.callee (-fr) (-160) 0).Off (k - -fr) →
      Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 := fun k hk hn =>
    hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo (by decide) hkc (by omega) (by decide) (by decide) hk hn)
  refine ⟨Spike.Lib.A64.Flow.FStable.callee hR hlo (by decide) hkc (by omega) hF m m' hFm hd,
    fun k hk hn => ?_, mC, σC, c, hA, hJ, hN, fun k hk hn => (hsep k hk hn).trans (hK k hk hn)⟩
  rw [hsep k hk hn]
  exact hcc k hk hn

/-- **The stack range off the allocator's region** under `AllocW2`'s frame
condition (`stackOff_callee`): off the caller's region (`hFO`) or a caller's
cell outside the allocator's (`CallerCells`). -/
theorem stackOff_allocCtx {rS : Range} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hlo : R.lo ≤ -fr + -160) (hkc : -fr < R.hi) (hk8 : fr % 8 = 0)
    (hFO : ∀ m, F m → StackOff rS R m) :
    ∀ m, (F m ∧ CallerCells R (-fr) (-160) 0 m ∧ AllocCtx ms L R fr Jc q m) →
      StackOff rS (R.callee (-fr) (-160) 0) m := fun m hm =>
  Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hR hb hl hh hlo (by decide) hkc (by omega) (hFO m hm.1) hm.2.1

end Frame

/-! ## The call's control -/

section Ctl

variable {p : Prog} {lbl : Lbl} {lsize : Lsize} {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
  {t : Expr} {env : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
  {a0 a1 a2 : Scc.IR.Operand}

/-- **The call's control is free of `ZBad`** under the call's context at the
call node past `nbJ1` (`allocW2`'s `hG0F`): it is the ghost `c0`'s after
`nbJ1`'s local run (`FrOk2.run`, `FrameRun.ofLocal`). -/
theorem frOk2_allocCtx (hp : ProgNoS ZBad p) {fs : List TermRun.Frame} (hc0 : FrOk2 c0 fs)
    {ms : MemSide isaLSE2} {L : Label → Int64} {R : Region} {pcB : Int64} {q : Call} {F : MachineData → Prop} :
    ∀ m, (F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
        AllocCtx ms L R cx.frame (nbJc L [blD Scc.Lower.Names.alloc] pcB (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) q m) →
      FrOk2 q.c0 fs := by
  rintro m ⟨-, -, mC, σC, c1, -, ⟨σ0, hJ, -⟩, hN, -⟩
  have hc1 : c1 = q.c0 := hN.1
  subst hc1
  exact Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hJ.2.2.2.2.2.1 fs) hc0

end Ctl

/-! ## The allocator field -/

section Field

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop} {a : Int64}

/-- **`AllocW2`'s allocator field at `W₀ := W2`** for one call `q` with its
premises (`hq`) returning into the entry's phase off the write abort (`hra`,
`hraAb`), at an allocation's call node past `nbJ1` (the walk's facts at the
allocation's `let` `t`: `htot`, `hlb`, `himm`; the ghost `c0` free of
`ZBad`, `hc0`), at a family `J` containing the starts with the self-segment
pairs (`StartsS … (Sg2 …)`, `hJ`) and a reachable placement (`hRe`): every
node of `scc_rt_alloc` inside `W2` over `IN … J` at the frames `fs`, in the
allocator's region under `AllocW2`'s frame condition. `allocW2X` with the
frame condition's stability and stack range (`fstable_allocCtx`,
`stackOff_allocCtx`), the call's control (`frOk2_allocCtx`), the placement
(`allocHP`, `slotRep_nbJ1`, the frames placed under `F`, `hfp`) and the
counter add's held landing in the family (`pendA_of_selfN`) by its own
segment (`allocHeld_sg2`, from the landings' allocation fragment `hxa` and
the heap abort path's obligations `hstub` at every family containing
`StartsN`; `allocHeld_nr`). The allocator's `W2` is relative to the thread
pointer `TP tp` (`nbCall_seg` supplies it at the call), so the held pair
starts at `n4` with `TP tp` and `hxa` is asked at `TP tp`. -/
theorem allocW2_w2 {rS : Range} (hI : InstOk exe endPc prog lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOkR lab = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int) + -160 - 48) (hhi : 0 ≤ R.hi) (hFS : FStable R F)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isaLSE2} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {J : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab) S0 Es L ls s c fs → J L ls s c fs)
    (hRe : Reach ar L0 ls0 lbl lsize)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) y).isSome)
    (hlb : Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2 env) t)
    (himm : Spike.Lib.LowerNode.ImmIn Λ.imms (Spike.Lib.LowerNode.ofEnv2 env) t) (hc0 : FrOk2 c0 fs)
    {pcB : Int64} {q : Call}
    (hq : q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
      (_root_.Executable.labels exe).label)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hxa : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0)
          (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
            AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
              (_root_.Executable.labels exe).label R
              cx.frame
              (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
                (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) q m)
          (Spike.Lib.A64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hstub : ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R cx.frame
        (fun σC => nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2) σC q.c0)).J σC c0' →
      Spike.Lib.A64.Abort.Disp.StubHW
        (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) p lbl (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-(cx.frame : Int) + -160) (-48) 0)
        (fun m => F m ∧ CKept R (-(cx.frame : Int) + -160) (-48) 0 m0 m ∧
          Abs R ⟨-(cx.frame : Int) + -160, []⟩ m0 σC) c0') :
    AllocW (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) q
      (fun s c => TP tp s → W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs)
      (TakeK a rS) exe endPc
      (R.callee (-(cx.frame : Int)) (-160) 0)
      (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
        AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
          (_root_.Executable.labels exe).label R
              cx.frame
          (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
            (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) q m) := by
  have hlab := hI.labOk
  subst hlab
  have hge := frame_ge16 hf
  have hlo1 : R.lo ≤ -(cx.frame : Int) + -160 := by omega
  have hkc : -(cx.frame : Int) < R.hi := by omega
  have hk8 : (cx.frame : Int) % 8 = 0 := by omega
  have hRc := Region.callee_ok (hi' := 0) hR hlo1 (by decide) hkc (by omega)
  have halc : (R.callee (-(cx.frame : Int)) (-160) 0).base.toNat % 16 = 0 := by
    have hb := Region.callee_base (hi' := 0) hR hlo1 (by decide) hkc
    omega
  have hFc := fstable_allocCtx (ms := msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
    (L := (_root_.Executable.labels exe).label)
    (Jc := nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
      (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) (q := q) hR hFS hlo1 hkc hk8
  have hFOc := stackOff_allocCtx (ms := msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
    (L := (_root_.Executable.labels exe).label)
    (Jc := nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
      (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) (q := q) hR (by omega) hl hh hlo1 hkc hk8 hFO
  have hP := allocHP (Λ := Λ) (fs := fs) hf h16 hR (by omega) hhi hFS hfp
    (ms := msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
    (L := (_root_.Executable.labels exe).label) (pcB := pcB) (q := q)
    (slotRep_nbJ1 (p := p) (lsize := lsize) (fp := fp) (ra := ra) (tp := tp) (c0 := c0) (lits := lits) (cs := cs)
      (bufs := bufs) (a0 := a0) (a1 := a1) (a2 := a2) htot hlb himm)
  have hcode : Spike.Lib.A64.Alloc.Code (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) q
      exe endPc := Spike.Lib.A64.Flow.alloc_code_of hI.lays hI.endOk hA
  have hQ := allocHeld_sg2 (I0 := IN ar L0 ls0 J) (S0 := S0) (Es := Es) (Dt := Dt) hI hA hph habk hown hRc halc
    (Int.le_refl _) (Int.le_refl _) (show (-160 : Int) % 8 = 0 by decide)
    (show (0 : Int) % 8 = 0 by decide) hsub hfit hFOc hp hq hra hraAb
    (fun a h m hm => hmem a h m hm.1) hno hlt h64 (frOk2_allocCtx hp hc0) hP hFc hcode hxa hFS hR hal
    (by omega) hlo (by omega) (leaveOk_of_allocCtx fun m hm => ⟨hm.1, hm.2.2⟩) hstub
  refine allocW2X hI hA hph habk hown hRc halc (Int.le_refl _) (Int.le_refl _) (show (-160 : Int) % 8 = 0 by decide)
    (show (0 : Int) % 8 = 0 by decide) hsub hfit hFOc hFc hp (fun _ _ => hq) hra hraAb
    (fun a h m hm => hmem a h m hm.1) hno hlt h64 (frOk2_allocCtx hp hc0) hP ?_
  exact fun s c h ht => pendA_of_selfN hJ hRe hQ (fun _ _ h => ⟨h, rfl⟩) (fun _ _ h _ => allocHeld_nr hq h.1) s c
    ⟨h, ht⟩

/-- **`AllocW2`'s allocator field at `W₀ := W2`**, for every call with its
premises returning past the `bl` at `pcB` (`allocW2_w2` at each): the
return's phase and its being off the write abort from the landing `pcB + 4`
(`hraP`, `hraAbP`); the counter and the headers unmapped and owned at no
phase (`hmem`, `hno`), the landings' allocation fragment (`hxa`) and the
heap abort path's obligations without code (`StubHN`, as `stubHN_w2` gives
them; `StubHN.stubHW` with the abort code `hprA`) for every such call. -/
theorem allocW2_field {rS : Range} (hI : InstOk exe endPc prog lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOkR lab = true) (hprA : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {Λ : Scc.Sem.Layout}
    {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int) + -160 - 48) (hhi : 0 ≤ R.hi) (hFS : FStable R F)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isaLSE2} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {J : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab) S0 Es L ls s c fs → J L ls s c fs)
    (hRe : Reach ar L0 ls0 lbl lsize)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {a0 a1 a2 : Scc.IR.Operand}
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) y).isSome)
    (hlb : Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2 env) t)
    (himm : Spike.Lib.LowerNode.ImmIn Λ.imms (Spike.Lib.LowerNode.ofEnv2 env) t) (hc0 : FrOk2 c0 fs)
    {pcB : Int64}
    (hraP : ph (pcB + 4).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAbP : pcB + 4 ∉ abPcs lab)
    (hmem : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ a : BitVec 64, (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hxa : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0)
          (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
            AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
              (_root_.Executable.labels exe).label R
              cx.frame
              (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
                (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) q m)
          (Spike.Lib.A64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hstub : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R cx.frame
        (fun σC => nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2) σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-(cx.frame : Int) + -160) (-48) 0)
        (fun m => F m ∧ CKept R (-(cx.frame : Int) + -160) (-48) 0 m0 m ∧
          Abs R ⟨-(cx.frame : Int) + -160, []⟩ m0 σC) c0') :
    ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label → q.ra = (pcB + 4).toBitVec →
      AllocW (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) q
        (fun s c => TP tp s → W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) exe
        endPc (R.callee (-(cx.frame : Int)) (-160) 0)
        (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
          AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
            (_root_.Executable.labels exe).label R cx.frame
            (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc] pcB (oF cx)
              (nbJ1 p lbl lsize cx fp ra tp c0 t env lits cs bufs a0 a1 a2)) q m) := by
  intro q hq hqra
  have hge := frame_ge16 hf
  have hra' : Int64.ofBitVec q.ra = pcB + 4 := by rw [hqra]; rfl
  refine allocW2_w2 hI hA hph habk hown hf h16 hR hal hl hh hlo hhi hFS hsub hfit hFO hp hJ hRe hfp htot hlb himm
    hc0 hq (by rw [hra']; exact hraP) (by rw [hra']; exact hraAbP) (hmem q hq) (hno q hq) hlt h64 (hxa q hq)
    fun J' hJ' m0 σC c0' hH => ?_
  have hK : (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).K =
      some Scc.Sem.A64.abi := by cases ab <;> rfl
  exact (hstub q hq J' hJ' m0 σC c0' hH).stubHW hI.lays hI.endOk hprA hK
    (Spike.Lib.A64.Flow.fstable_enter (kc := -(cx.frame : Int) + -160) hR hFS (by omega) (by decide) (by omega)
      (by decide) (by omega) (by decide) (by decide))

end Field

/-- info: 'Spike.Lib.LowerA64.fstable_allocCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fstable_allocCtx

/-- info: 'Spike.Lib.LowerA64.stackOff_allocCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackOff_allocCtx

/-- info: 'Spike.Lib.LowerA64.frOk2_allocCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frOk2_allocCtx

/-- info: 'Spike.Lib.LowerA64.allocW2_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2_w2

/-- info: 'Spike.Lib.LowerA64.allocW2_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2_field

end Spike.Lib.LowerA64
