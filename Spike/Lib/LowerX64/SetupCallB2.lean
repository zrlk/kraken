/-
**The setup block's call at a known frame condition, from its exits by
placements** (x86-64; the twin of `Spike/Lib/LowerA64/SetupCallB2.lean`):
the producers of `SetupCallWS` (`setupCallWS_framed`,
`Spike/Lib/LowerX64/SetupCall2.lean`; `setupCallWS_ofFnSpec`,
`Spike/Lib/LowerX64/SetupCallC2.lean`; `setupCallWS_ofPlaceOK`,
`Spike/Lib/LowerX64/HproSetupP.lean`) at `SetupCallWSB`
(`Spike/Lib/Rt/X64MainSSB.lean`): their per-call premise (`hseg`, `hpre`)
may assume `Fs F' g fr` of the frame condition, the ghost and the frame,
e.g. `SetupGF` (the frame condition `call_ndSG`'s ghost frame condition at
`scc_rt_main`'s call node), so that the setup function's context can record
the suspended caller below its frames.

- `setupCallWSB_framed`, `setupCallWSB_ofFnSpec`, `setupCallWSB_ofPlaceOK`:
  `setupCallWS_framed`, `setupCallWS_ofFnSpec`, `setupCallWS_ofPlaceOK` at
  `SetupCallWSB … Fs`, the premise `Fs F' g fr` passed to theirs.
- `setupCallWSB_ofPlaceOKC`: `setupCallWSB_ofPlaceOK` at any code facts `c` (immediates included)
  with its prologue's facts `ProOK` and the return address in `RaOk`.
-/
import Spike.Lib.LowerX64.HproSetupP
import Spike.Lib.LowerX64.SetupCallC2
import Spike.Lib.Rt.X64MainSSB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW CallTo)
open Spike.Lib.X64Consumer (K0 Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedS InvS envsOf fvOf termsOf)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA LimOk WcG CallerCells)
open Spike.Lib.LowerNode (FrOk2 ZBad setupK compiled2 RetL)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
  {cells : List (Directive × Nat)} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The framed setup block at a known frame condition, from its exits**
(`setupCallWS_framed` at `SetupCallWSB … Fs`). -/
theorem setupCallWSB_framed {Fs : (MachineData → Prop) → WcG → TermRun.Frame → Prop}
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {ty : Ty} {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.X64.Flow.Ret0.CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ (g : Spike.Lib.X64.Flow.Ret0.WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr →
      Fs F' g fr →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (Ab : FragS isa) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g)).at [fr])
          (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' g.fp g.ra tp c0' [fr]
            ty Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.SetupCallWSB W K p lbl ms exe endPc R F fn Z D ZU (SRetR lbl ty) ra c0 tp Fs := by
  intro F' hR0 hF' hFF g fr hra htp hct hFs
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hF' hFF g fr hra htp hct hFs hbase
  refine (SegWS.seq_left (Q := Ab) (E := (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
      (Spike.Lib.X64.Rt.uNxS (SRetR lbl ty) g)).at [fr]) (h1.mono_post fun s c fs h => ?_) hAb).mono_post
      fun s c fs h => ?_
  · rcases h with ⟨rfl, c1, -, hA⟩ | h
    · exact .inr ⟨uPostSR_ret hbase htp.symm hA, rfl⟩
    · exact .inl h
  · exact h.elim False.elim id

omit [Kraken.Executable.ValidLayout exe] in
/-- **The setup block at a known frame condition from the setup function's
segment** (`setupCallWS_ofFnSpec` at `SetupCallWSB … Fs`). -/
theorem setupCallWSB_ofFnSpec {Fs : (MachineData → Prop) → WcG → TermRun.Frame → Prop}
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hs : FnSpecC2 W K p lbl lsize ms CxOk c)
    (hu : d.argTy = .unit) (hna : c.na = 0)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {ra : BitVec 64}
    {c0 : Ctl} {tp : UInt64} (hfn : fn = c.fn) (hZU : ZU = Int64.ofInt c.fr.size)
    (hcE : ∀ cE fr, CallTo p c0 cE fr → cE = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hms : ∀ fr a Z', LimOk (ms []) F a Z' → LimOk (ms [fr]) F a Z')
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ra → g.tp = tp → CallTo p c0 g.c0 fr → Fs F' g fr →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (ProEdge2 p lbl lsize (ms [fr]) F' c g.fp g.ra tp g.c0
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g).J →
          CalleePre2 W K p lbl lsize ms CxOk c (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [fr] g.fp g.ra tp G0
            Ab (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g).J g.c0) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.SetupCallWSB W K p lbl ms exe endPc R F fn Z D ZU (SRetR lbl d.retTy) ra c0 tp Fs := by
  refine setupCallWSB_framed fun F' hR0 hF' hFF g fr hra htp hct hFs hbase => ?_
  obtain ⟨G0, Ab, hP, hAb⟩ := hpre F' hR0 hF' hFF g fr hra htp hct hFs hbase
  obtain ⟨zs, hsp⟩ := c.hsp
  rw [hna] at hsp
  have hedge := proEdge2_ofUN0 (p := p) (lbl := lbl) (lsize := lsize) c hu (hna ▸ c.henv) c.hlits hsp
    (hcE _ _ hct) hZU (hms fr) (fun m hm => (hFF m hm).1)
    (J := (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label (ms []) F fn ZU g).J)
    fun _ _ h => h
  rw [htp] at hedge
  have H := (hP hedge).seg hs (List.cons_ne_nil _ _)
  subst hfn
  exact ⟨Ab, g.c0, H, hAb⟩

end Fn

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

variable {d : Decl} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {T : Expr → Prop} {rS : Range} {Λw : Scc.Sem.Layout} {lbl : Lbl} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lsize : Lsize}

/-- **The setup call at a known frame condition from the placement check, at any
code facts** (`setupCallWSB_ofPlaceOK`'s proof): the setup function's code facts `c`
at any immediates `im`, call and code predicates, with its prologue's facts
(`hc`) and the return address past the setup call in `RaOk` (`hraS`). -/
theorem setupCallWSB_ofPlaceOKC {Fs : (MachineData → Prop) → WcG → TermRun.Frame → Prop}
    {im : Expr → String → Nat → Option Nat} (c : FnCode2 (LY).exe (LY).prog (LY).endPc RaOk Cd im T d)
    (hc : ProOK LY d c) {sw : Nat} (hraS : RaOk ((LY).lab (setupMC sw).sp0).toBitVec)
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hs : FnSpecC2 (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk c)
    (hu : d.argTy = .unit) (hna : c.na = 0)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64}
    {tp : UInt64} {c0 : Ctl} {meW : TermRun.Word} {n : Nat}
    (hfn : fn = c.fn) (hZU : ZU = Int64.ofInt c.fr.size)
    (hc0 : c0 = ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩)
    (hcE : ∀ cE fr, CallTo p c0 cE fr → cE = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hms : ∀ fr a Z', LimOk (ms []) F a Z' → LimOk (ms [fr]) F a Z')
    (hL : PosOff OP (LY).lab ((LY).lab (proL c.fr)))
    (himm : Λw.imms setupK "me" 0 = some n) (hv : ValRep lbl meW.val n)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ((LY).lab (setupMC sw).sp0).toBitVec → g.tp = tp →
      CallTo p c0 g.c0 fr → Fs F' g fr → (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (ProEdge2 p lbl lsize (ms [fr]) F' c g.fp g.ra tp g.c0
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU g).J →
          CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
              (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
            (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk c rS
            (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [fr] g.fp g.ra tp G0 Ab
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU g).J g.c0) ∧
        FrOk2 g.c0 [fr] ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.SetupCallWSB
      (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU (SRetR lbl d.retTy)
      ((LY).lab (setupMC sw).sp0).toBitVec c0 tp Fs := by
  refine setupCallWSB_ofFnSpec c hs hu hna hfn hZU hcE hms
    fun F' hR0 hF' hFF g fr hra htp hct hFs hbase => ?_
  obtain ⟨G0, Ab, hP, hfo, hAb⟩ := hpre F' hR0 hF' hFF g fr hra htp hct hFs hbase
  refine ⟨G0, Ab, fun he => ?_, hAb⟩
  have hP' := hP he
  refine hP'.toPre ?_ ?_
  · rw [hra]; exact hraS
  · subst hc0
    exact hpro_setup_ofPlaceOKP h c hc hL
      hP'.hR hP'.hR8 hP'.hlo (by have := hP'.hhi; omega) hP'.hl hP'.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP'.hFO hpN (placedS_setupCall hct himm hv) hfo

/-- **The setup call at a known frame condition from the placement check**
(`setupCallWS_ofPlaceOK` at `SetupCallWSB … Fs`). -/
theorem setupCallWSB_ofPlaceOK {Fs : (MachineData → Prop) → WcG → TermRun.Frame → Prop}
    {j : Nat} (hd : (compiled2 p)[j]? = some d)
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hs : FnSpecC2 (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd))
    (hu : d.argTy = .unit) (hna : (fnCode2OfP hp h j d hd).na = 0)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {sw : Nat}
    {tp : UInt64} {c0 : Ctl} {meW : TermRun.Word} {n : Nat}
    (hfn : fn = (fnCode2OfP hp h j d hd).fn) (hZU : ZU = Int64.ofInt (fnCode2OfP hp h j d hd).fr.size)
    (hc0 : c0 = ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩)
    (hcE : ∀ cE fr, CallTo p c0 cE fr → cE = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hms : ∀ fr a Z', LimOk (ms []) F a Z' → LimOk (ms [fr]) F a Z')
    (hL : PosOff OP (LY).lab ((LY).lab (proL (fnCode2OfP hp h j d hd).fr)))
    (himm : Λw.imms setupK "me" 0 = some n) (hv : ValRep lbl meW.val n)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ((LY).lab (setupMC sw).sp0).toBitVec → g.tp = tp →
      CallTo p c0 g.c0 fr → Fs F' g fr → (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa),
        (ProEdge2 p lbl lsize (ms [fr]) F' (fnCode2OfP hp h j d hd) g.fp g.ra tp g.c0
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU g).J →
          CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
              (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
            (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd) rS
            (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [fr] g.fp g.ra tp G0 Ab
            (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU g).J g.c0) ∧
        FrOk2 g.c0 [fr] ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.SetupCallWSB
      (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU (SRetR lbl d.retTy)
      ((LY).lab (setupMC sw).sp0).toBitVec c0 tp Fs :=
  setupCallWSB_ofPlaceOKC h (fnCode2OfP hp h j d hd) (fnCode2OfP_spec hp h j d hd).2.2
    (raOk_setup LY sw) hs hu hna hfn hZU hc0 hcE hms hL himm hv hmr hun hsub hfit hpN hpre

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.setupCallWSB_framed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupCallWSB_framed

/--
info: 'Spike.Lib.LowerX64.setupCallWSB_ofFnSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupCallWSB_ofFnSpec

/--
info: 'Spike.Lib.LowerX64.setupCallWSB_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupCallWSB_ofPlaceOK

/--
info: 'Spike.Lib.LowerX64.setupCallWSB_ofPlaceOKC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupCallWSB_ofPlaceOKC
