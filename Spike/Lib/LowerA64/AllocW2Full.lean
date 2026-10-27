/-
**A buffer allocation's `AllocW2` at `W₀ := W2`** (AArch64): the full
premise of `newBufC_of` for one allocation `let x = newBuf cn τ in e` at the
code `CdCLE` and the calls `BlC2L` (as `FnCode2Build` gives them), its fields from

- the arguments' loads `allocArgs_w2`, the `bl` `allocBl_w2`, the returned
  base's store `allocStore_w2` at every placement extending the call's
  (`Spike/Lib/LowerA64/AllocW2W2.lean`; the frames placed at a larger label
  map, `framesPlacedInI_mono_lbl`);
- the call's arguments `allocHq`;
- the allocator's field `allocW2_field` (`Spike/Lib/LowerA64/AllocFieldW2.lean`),
  the return's phase the allocator's entry's (`blC2_hra`), the
  return off the write abort as the store's start (`CdCLE`, `posOff_start`,
  `notAbPc_of_posOff`);
- the counter and headers unmapped (`hmem`), the landings' allocation fragment
  (`hxa`, e.g. `landStk_hxa`) and the sizes (`hsz`) taken as premises.
-/
import Spike.Lib.LowerA64.AllocFieldW2
import Spike.Lib.LowerA64.FnCodeLE
import Spike.Lib.LowerA64.AllocRa

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (BlkW At FStable CKept Abs AS blD)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK CallerCells)
open Spike.Lib.A64.Flow.NewBuf (AllocCtx nbJc)
open Spike.Lib.A64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.AllocG (allocPhOk allocAbOk)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.AllocReach (Reach IN)
open Scc.Emit.A64 (FnCtx directives)
open Scc.Lower.InvA64 (FrameOk)

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
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop} {a : Int64}

/-- **`AllocW2` at `W₀ := W2`** for the allocation `let x = newBuf cn τ in e`
at `pc` (the header `h`, the count `kv`, the units `u`), at the code
`CdCLE … ra0` and the calls `BlC2L … cx ra0`: the arguments' loads, the `bl`
and the returned base's store inside `W2` (`allocArgs_w2`, `allocBl_w2`,
`allocStore_w2`, the frames `hfp` placed at every larger label map), the
call's arguments (`allocHq`: `hg`, `hcn`, `hsc`, `hleaf`, `hu`, `hacc`,
`hms`), the allocator's field (`allocW2_field`, the return's phase the
allocator's by `blC2_hra`) and the premises `hmem`, `hxa`, `hsz` at every `bl`
pc. -/
theorem allocW2_w2Full {rS : Range} (hI : InstOk exe endPc prog lab μ own Tk (TakeK a rS) okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (habk : allocAbOk lab = true) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hprA : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {Λ : Scc.Sem.Layout} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s))) {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    (h16 : cx.frame % 16 = 0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
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
    {ra0 : Int64} (hrs : ∀ r k, Spike.Lib.LowerA64.rsOf cx r = some k → R.Off k)
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
    (hu : ∀ sl, Spike.Lib.Form.opdVal (Spike.Lib.LowerA64.rsOf cx) sl u =
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
    (hxa : ∀ la : List Scc.Emit.A64.Item, cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la →
      ∀ q : {q : Call // q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label R cx.frame
        (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
          (pc + Int64.ofNat (4 * (directives la).length)) (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv) u))
        q.1 m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0) F'
        (Spike.Lib.A64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) q.1 l b w)
        s c → TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs).xa l b w s c)
    (hxaF : ∀ la : List Scc.Emit.A64.Item, cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la →
      ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ l b w s c, lbl l = none →
        At exe endPc (R.callee (-(cx.frame : Int)) (-160) 0)
          (fun m => F m ∧ CallerCells R (-(cx.frame : Int)) (-160) 0 m ∧
            AllocCtx (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
              (_root_.Executable.labels exe).label R cx.frame
              (nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
          (pc + Int64.ofNat (4 * (directives la).length)) (oF cx)
                (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
                  (.imm kv) u)) q m)
          (Spike.Lib.A64.Alloc.Ea (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q l b w)
          s c →
        TP tp s → (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs).xa l b w s c)
    (hstub : ∀ la : List Scc.Emit.A64.Item, cx.getArgs [Scc.Lower.imm h, .imm kv, u] = .ok la →
      ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label →
      ∀ J' : InvS, (∀ L ls, Reach ar L0 ls0 L ls → ∀ s c fs, StartsN ar L0 ls0 S0 Es L ls s c fs →
        J' L ls s c fs) →
      ∀ m0 σC c0', (HeldAb (_root_.Executable.labels exe).label
        (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) q lbl R cx.frame
        (fun σC => nbJc (_root_.Executable.labels exe).label [blD Scc.Lower.Names.alloc]
          (pc + Int64.ofNat (4 * (directives la).length)) (oF cx)
          (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv) u)
          σC q.c0)).J σC c0' →
      StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J') Dt (Ab lab) lbl lsize s c fs)
        (TakeK a rS) (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J') ab lbl lsize fs) exe endPc
        (R.callee (-(cx.frame : Int) + -160) (-48) 0)
        (fun m => F m ∧ CKept R (-(cx.frame : Int) + -160) (-48) 0 m0 m ∧
          Abs R ⟨-(cx.frame : Int) + -160, []⟩ m0 σC) c0')
    (hsz : ∀ q : Call, q.OK (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs)
        (_root_.Executable.labels exe).label → ∀ l b old, lbl l = some b →
      b = ar.heap + 16 * old + ar.off q.n q.τ → old + ar.units q.n q.τ ≤ ar.cells → q.n ≤ lsize l) :
    AllocW2 (CdCLE prog okPc ph lab ra0) (BlC2L prog okPc ph lab cx ra0)
      (fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar (IN ar L0 ls0 J) Dt (Ab lab) lbl lsize s c fs) (TakeK a rS)
      exe endPc R F (msOfAX Λ μ p rd G (fun s _ => own s) ar (IN ar L0 ls0 J) ab lbl lsize fs) lbl lsize tp cx pc
      (Scc.Lower.Inv.regName x n) h kv u
      (laneJ p lbl lsize Λ.imms cx fp ra tp c0 pc (.let_ x (.newBuf cn τ) e) env lits cs bufs)
      (nbJ1 p lbl lsize cx fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h) (.imm kv) u) := by
  have hlab := hI.labOk
  subst hlab
  have hge := frame_ge16 hf
  have hlo1 : R.lo ≤ -(cx.frame : Int) := by omega
  intro la ls k hla hls L pcB pcR Jc hCd hBl hCd'
  have hne : directives ls ≠ [] := by
    have hls' := hls
    obtain ⟨off, hoff, -⟩ := bind_eq_ok hls'
    rw [Scc.Lower.InvA64.setReg_eq hf (by omega) hoff] at hls'
    cases ok_inj hls'
    simp [directives, Scc.Emit.A64.ins]
  have hraAbP : pcB + 4 ∉ abPcs (_root_.Executable.labels exe).label :=
    notAbPc_of_posOff hI.lays hpr hprA (posOff_start hCd'.1 hne)
  have hraP : ph (pcB + 4).toBitVec.toNat = ph ((_root_.Executable.labels exe).label "scc_rt_alloc").toBitVec.toNat :=
    (blC2_hra hBl.1).symm
  refine ⟨allocArgs_w2 hI hpr hprA hf h1 h16 hR hal hlo1 hhi hl hh hsub hfit hFO hFS hp hrs hfp
      (fun _ h => by cases h) hc0 hla hCd,
    allocBl_w2 hI hpr hprA hA hR hal hlo1 hhi hl hh hsub hfit hFO hFS hp hBl.1.1 hrs hfp (fun _ h => by cases h) hc0
      htot hlb himm,
    allocHq hg hcn hsc hleaf hu hacc hms, by cases ab <;> exact hmem, hxa la hla,
    allocW2_field hI hA hph habk hprA hown hf h16 hR hal hl hh hlo hhi hFS hsub hfit hFO hp hJ hRe hfp htot hlb himm
      hc0 hraP hraAbP hmem hno hlt h64 (hxaF la hla) (hstub la hla), by cases ab <;> exact hsz, fun lbl' lsize' hl' _ => ?_⟩
  exact allocStore_w2 hI hpr hprA hf h1 h16 hR hal
    (by simp only [Spike.Lib.A64.Flow.NewBuf.allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega) hhi hl hh
    hsub hfit hFO hFS hp hrs (fun s hs => (hfp s hs).imp fun _ hB => framesPlacedInI_mono_lbl hl' hB) he2 hfr hl'
    hnr hc0 hls hCd' hIt hIc hlbe

end Full

/-- info: 'Spike.Lib.LowerA64.framesPlacedInI_mono_lbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms framesPlacedInI_mono_lbl

/-- info: 'Spike.Lib.LowerA64.allocW2_w2Full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW2_w2Full

end Spike.Lib.LowerA64
