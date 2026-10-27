/-
**A buffer allocation's `AllocW2` at `W₀ := W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/AllocW2Full.lean`): the full premise of `newBufC_of`
for one allocation `let x = newBuf cn τ in e` at the code `CdCLE` and the
calls `BlC2L`, its fields from

- the arguments' loads `allocArgs_w2`, the `callq` `allocBl_w2`, the
  returned base's store `allocStore_w2` at every placement extending the
  call's (`Spike/Lib/LowerX64/AllocW2W2.lean`; the frames placed at a larger
  label map, `framesPlacedInI_mono_lbl`);
- the call's arguments `allocHq`;
- the allocator's field `allocW2_field` (`Spike/Lib/LowerX64/AllocFieldW2.lean`),
  the return's phase the allocator's by the `callq`'s (`BlC2`, `blC2_hra`),
  the return off the write abort as the store's start (`CdCLE`,
  `posOff_start`, `notAbPc_of_posOff`);
- the counter and headers unmapped (`hmem`), the landings' allocation fragment
  (`hxa`, at the call's own argument block and `callq`, `landStk_hxa`'s
  shape) and the sizes (`hsz`) taken as premises.

Unlike the AArch64 twin, the `callq`'s size `zc` is a cell of the layout
(the return at `pcB + zc`, not `pcB + 4`), so the per-call premises `hxaF`,
`hstub` are taken at every `callq` pc `pcB` and size `zc` (`hxa` at the
argument block `lw`, its sizes `zs` and the `callq` of size `zc` after it); the
allocator's region is `8` bytes deeper (the pushed return address,
`R.callee (-fr - 8) (-160) 8`).
-/
import Spike.Lib.LowerX64.AllocFieldW2
import Spike.Lib.LowerX64.AllocW2W2
import Spike.Lib.LowerX64.FnCodeLE
import Spike.Lib.LowerX64.AllocRa

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (BlkW At FStable CKept Abs AS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK CallerCells)
open Spike.Lib.X64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.X64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Alloc (Call AllocW)
open Spike.Lib.X64.AllocG (allocPhOk allocAbOk)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.AllocReach (Reach IN)

/-- **The suspended frames placed at more placed labels** (`valRep_mono`,
`LocRep.mono_lbl` at each word place). -/
theorem framesPlacedInI_mono_lbl {Λ : Scc.Sem.Layout} {lbl lbl' : Lbl} {s : State} {fs : List TermRun.Frame}
    {A : Nat → Prop} (hl : ∀ l b, lbl l = some b → lbl' l = some b) (h : FramesPlacedInI Λ lbl s fs A) :
    FramesPlacedInI Λ lbl' s fs A := by
  obtain ⟨envm, hrep, htot, hin, himm⟩ := h
  refine ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp => ?_, htot, hin, himm⟩
  have hr := hrep d f hf x ty ws hx k wd wp hwd hwp
  match wp, hr with
  | .one pl, ⟨v, hv, hr⟩ => exact ⟨v, hv, Scc.Sem.MemRel.valRep_mono hl hr⟩
  | .loc pb po, ⟨vb, vo, hb, ho, hr⟩ =>
    refine ⟨vb, vo, hb, ho, ?_⟩
    cases hv : wd.val with
    | loc a tag => rw [hv] at hr; exact ⟨hr.1, hl _ _ hr.2.1, hr.2.2⟩
    | undef => trivial
    | _ => rw [hv] at hr; exact hr.elim
  | .imm n, hr => exact Scc.Sem.MemRel.valRep_mono hl hr

section Full

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop} {a : Int64}

/-- **`AllocW2` at `W₀ := W2`** for the allocation `let x = newBuf cn τ in e`
at `pc` (the header `h`, the count `kv`, the units `u`), at the code
`CdCLE … ra0` and the calls `BlC2L … fr ra0`: the arguments' loads, the
`callq` and the returned base's store inside `W2` (`allocArgs_w2`,
`allocBl_w2`, `allocStore_w2`, the frames `hfp` placed at every larger
label map), the call's arguments (`allocHq`: `hg`, `hcn`, `hsc`, `hleaf`,
`hu`, `hacc`, `hms`), the allocator's field (`allocW2_field`, the return's
phase the allocator's by `blC2_hra`) and the premises `hmem`, `hxa`, `hsz`
at every `callq` pc and size. -/
theorem allocW2_w2Full {rS : Range} (hI : InstOk exe endPc cells lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hprA : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (h16 : fr.size % 16 = 0) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 + -160 - 32) (hhi : 16 ≤ R.hi) (hFS : FStable R F)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {p : Prog} (hp : ProgNoS ZBad p) {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {S0 : FragS isa} {Es : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {J : InvS} {ab : Option (State → Prop)} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    {fs : List TermRun.Frame}
    (hJ : ∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs,
      StartsS ar L0 ls0 (Sg2 Λ μ p rd G own rS Tk ar L0 ls0 Dt (Ab lab) a ab) S0 Es L ls s c fs → J L ls s c fs)
    (hRe : Reach ar L0 ls0 lbl lsize)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ra0 : Int64} (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {x : String} {cn : At} {τ : Ty} {e : Expr}
    {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {h : Nat} {kv : UInt64} {u : Scc.IR.Operand} {tk : Ty} {pc : Int64}
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.newBuf cn τ) e),
      (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) y).isSome)
    (hlb : Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    (himm : Spike.Lib.LowerNode.ImmIn Λ.imms (Spike.Lib.LowerNode.ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    (hc0 : FrOk2 c0 fs) (he2 : Scc.Lower.elem2 τ = true) (hfr : Spike.Lib.LowerNode.Fresh env n)
    (hnr : fs = [] → ∀ a, e ≠ .ret a)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) y).isSome)
    (hIc : Spike.Lib.LowerNode.ImmIn Λ.imms (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hlbe : Spike.Lib.LowerNode.LocBaseRegAt (Spike.Lib.LowerNode.ofEnv2
      ((x, Spike.Lib.LowerShape.newBufTy τ, [.reg (Scc.Lower.Inv.regName x n), Scc.Lower.imm 0]) :: env)) e)
    (hg : Spike.Lib.LowerNode.GrpL env) (hcn : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hsc : Spike.Lib.LowerNode.InLits lits cn) (hleaf : ∃ o, Scc.Lower.litAt lits cn = .leaf o)
    (hu : ∀ sl, Spike.Lib.Form.opdVal (rsOf fr) sl u =
      some ((msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs).units kv.toNat τ))
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us)
    (hms : ∀ q : Call, q.n = kv.toNat → q.τ = τ → q.h = BitVec.ofNat 64 h →
      CallMsOK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label q)
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
    (hxa : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
      CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs) →
      BlC2L cells okPc ph lab fr ra0 (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : {q : Call // q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label R fr.size
        (nbJc (_root_.Executable.labels exe).label
          [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] (pc + Int64.ofNat zs.sum) (oB fr)
          (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
            (.imm kv) u))
        q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8) F'
        (Spike.Lib.X64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) q.1 l b w)
        s c → TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs).xa l b w s c)
    (hxaF : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
      CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs) →
      BlC2L cells okPc ph lab fr ra0 (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(fr.size : Int) - 8) (-160) 8)
          (fun m => F m ∧ CallerCells R (-(fr.size : Int) - 8) (-160) 8 m ∧
            AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
              (_root_.Executable.labels exe).label R fr.size
              (nbJc (_root_.Executable.labels exe).label
                [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] (pc + Int64.ofNat zs.sum)
                (oB fr)
                (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
                  (.imm kv) u)) q m)
          (Spike.Lib.X64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hstub : ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, u].zip Scc.Emit.X64.argRegs) = .ok lw → zs.length = (dirs lw).length →
      CdCLE cells okPc ph lab ra0 pc ((dirs lw).zip zs) →
      BlC2L cells okPc ph lab fr ra0 (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R fr.size
        (fun σC => nbJc (_root_.Executable.labels exe).label
          [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] (pc + Int64.ofNat zs.sum) (oB fr)
          (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
            (.imm kv) u) σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-(fr.size : Int) - 8 + -160 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 8 + -160, []⟩ m0 σC) c0')
    (hsz : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      b = ar.heap + 16 * old + ar.off q.n q.τ → old + ar.units q.n q.τ ≤ ar.cells → q.n ≤ lsize l) :
    AllocW2 (CdCLE cells okPc ph lab ra0) (BlC2L cells okPc ph lab fr ra0)
      (fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs) (TakeK a rS)
      exe endPc R F (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) lbl lsize tp fr pc
      (Scc.Lower.Inv.regName x n) h kv u
      (laneJ p lbl lsize Λ.imms fr fp ra tp c0 pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv)
        u) := by
  have hlab := hI.labOk
  subst hlab
  have h8 : (fr.size : Int) % 8 = 0 := by omega
  have hlo1 : R.lo ≤ -(fr.size : Int) := by omega
  intro lw off zs zc z k hlw hoff hz L pcB pcR B Jc hCd hBl hCd'
  have hraAbP : pcB + Int64.ofNat zc ∉ abPcs (_root_.Executable.labels exe).label :=
    notAbPc_of_posOff hI.lays hpr hprA (posOff_start hCd'.1 (by simp))
  have hraP : ph (pcB + Int64.ofNat zc).toBitVec.toNat =
      ph ((_root_.Executable.labels exe).label Spike.Lib.X64.Alloc.fnL).toBitVec.toNat :=
    (blC2_hra hBl.1).symm
  refine ⟨allocArgs_w2 hI hpr hprA hf h1 hR hR8 hlo1 hhi hl hh hsub hfit hFO hFS hp hrs hfp
      (fun _ h => by cases h) hc0 hlw hz hCd,
    allocBl_w2 hI hpr hprA hA h8 hR hR8 (by omega) hhi hl hh hsub hfit hFO hFS hp hBl.1.1 hrs hfp
      (fun _ h => by cases h) hc0 htot hlb himm,
    allocHq hg hcn hsc hleaf hu hacc hms, by cases ab <;> exact hmem, hxa lw zs zc k hlw hz hCd hBl,
    allocW2_field hI hA hph habk hprA hown hf h16 hR hR8 hl hh hlo (by omega) hFS hsub hfit hFO hp hJ hRe hfp
      htot hlb himm hc0 hraP hraAbP hmem hno hlt h64 (hxaF lw zs zc k hlw hz hCd hBl)
      (hstub lw zs zc k hlw hz hCd hBl), by cases ab <;> exact hsz,
    fun lbl' lsize' hl' _ => ?_⟩
  exact allocStore_w2 hI hpr hprA hf h1 hR hR8
    (by simp only [Spike.Lib.X64.Flow.NewBuf.allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega) hhi hl hh
    hsub hfit hFO hFS hp hrs (fun s hs => (hfp s hs).imp fun _ hB => framesPlacedInI_mono_lbl hl' hB) he2 hfr hl'
    hnr hc0 hoff hCd' hIt hIc hlbe

end Full

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.framesPlacedInI_mono_lbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.framesPlacedInI_mono_lbl

/-- info: 'Spike.Lib.LowerX64.allocW2_w2Full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2_w2Full
