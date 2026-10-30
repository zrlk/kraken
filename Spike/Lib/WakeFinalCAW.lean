/-
**wake.w's AArch64 statement with `D := wakeD`**:
`WakeFinalCAO.wake_finalCA_genO`/`genOP` at `WakeOD.wakeD` at the levels
(`WakeOPremW.W0W`, `W1W`) and the root's abort phases (`WakeOD.AbW`,
`AcW`), `hO` by `WakeOPremI.oPrem_WI` (the entry clear of the layout from
`Entry.Ok`), `hpc` by `A64WakeWcSeg.hpc_of` from `OpenW.hpost`.

- `wake_finalCA_genW`: `CorrectE 2` at every admissible entry, at any placed
  output. Open, per entry (`OpenW`): the segment `h0`, take facts and
  the start in `inv0` (`hst`); the segment `h1` and state after the
  `clone` (`hpost`) and clone facts (`hCl`); the counter row `hctr0`,
  the box store `hnew0`. Also
  open: the instance facts. `hpre` by `WakeHPre.hpre_of`: `hR1` the relation's
  first conjunct, `hr0`/`hr1` the root's constant ranges, `hG` by
  `WakeHG.memInv_gW` at the root's dummy heap word `cT E = WakeHG.cTW`.
- `wake_finalCA_genWP`: the same at the certificate's output `outLit`, the
  parses from one loader check `hP`.
- `iW Λ0 := WakeImmsC0.immsW2 Λ0 SccCode.wakeImms`, **the root's immediate
  table**: the certificate's, plus `me` at main's TCB at the start's term
  `main(me)` and at the box's term `wakeImm_t1` (where `wakeImms` has no
  entry, `wakeImms_startT`, `wakeImms_t1_me`: nothing is overridden);
  `iW_imms_c0W_me`, `iW_imms_c0W_z` its entries at the box. At the canonical layout `Λc`, `genWP` elaborates at
  `placeW_cert` with `i := iW Λc` (an `example`), and the start's control
  is placed at `L0T` there (`WakeImmsW.placedSE_startW`). The
  layout-specific instance facts (`hpin2`, `hinit2`, `hwide`, `hsub1`) do
  not read the table (the `example`s: equal at any two `i` by `rfl`), so
  deciding them at one `i` decides them at `iW`.

The write tail is `DtW`. The per-entry choices (`cT`, `ls0`, `Ctx`,
`frM`, `inv0`, `inv1`) are functions of the entry.
-/
import Spike.Lib.WakeFinalCAO
import Spike.Lib.WakeOPremI
import Spike.Lib.A64WakeWcSeg
import Spike.Lib.WakeImmsW
import Spike.Lib.WakeImmsC0
import Spike.Lib.WakeHG
import Spike.Lib.WakeHPre
import Spike.Lib.A64WakeCode

namespace Spike.Lib.WakeFinalCAW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.WakeMainHRD (MainSeg)
open Spike.Lib.WakeOPremW (W0W W1W)
open Spike.Lib.A64.WakeWf (DtW)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (cT : Entry → Loc) (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2)
  (frM : Entry → TermRun.Frame) (inv0 : Entry → FragS isaLSE2)
  (inv1 : Entry → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

/-- **wake's pre-spawn data at entry `E`**: `wakeD` at the levels. -/
abbrev DW (E : Entry) : WakeO.OData :=
  WakeOD.wakeD hp i E (cT E) DtW (ls0 E) (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (inv0 E)
    (W1W hp i E DtW (Ctx E) (ls0 E)) (inv1 E)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `DW` at the entry `E`. -/
local notation "DE" => DW hp i cT ls0 Ctx frM inv0 inv1 E

set_option hygiene false in
/-- The entry's marks. -/
local notation "μE" => (target (kernel 2) E).marks SccCertificate.asm (Ly).Λ

set_option hygiene false in
/-- The pre-spawn relation at `DW`. -/
local notation "R1W" => fun E d s => WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ)
  (DW hp i cT ls0 Ctx frM inv0 inv1 E) d s ∧ VPriv (Ly).Λ E d

/-- **The premises left open at `DW`**, per entry: the segment `h0`,
take facts and start `hst`; the segment `h1` and state after the `clone`
(`hpost`, `A64WakeWcSeg.ClonePost`); the counter row `hctr0`; the box store
`hnew0`. -/
structure OpenW (arch : WeakMem.Arch) (M : WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) (E : Entry) :
    Prop where
  h1 : ∀ l b n, (DE).L0 l = none → AllocLand (DE).ar.heap (DE).ar.cells b n →
    SegInvS ((DE).W1 l b n) (TakeCKS (DE).a (DE).Cl) wakeSrc (A64ConsumerA.upd (DE).L0 l b)
      (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (fun _ _ _ _ _ => False) (A64ConsumerA.upd (DE).L0 l b)
        (A64ConsumerA.updN (DE).ls0 l n)) ((DE).inv1 l b n)
  h0 : SegInvS (DE).W0 (TakeCKS (DE).a (DE).Cl) wakeSrc (DE).L0
    (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1) (DE).L0 (DE).ls0) (DE).inv0
  h1t : Spike.Lib.A64.Flow.WakeWc.H1Take (Ly) (WakeOSide.aW hp i E) (inv1 E)
  h1o : Spike.Lib.A64.Flow.WakeWc.H1TakeOwn (Ly) (WakeOSide.aW hp i E) (inv1 E)
  hst : inv0 E (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
    ⟨Spike.Lib.WakePreAsm.wakeTh0.term, Spike.Lib.WakePreAsm.wakeTh0.env, none⟩
    Spike.Lib.WakePreAsm.wakeTh0.stack
  hctr0 : ∀ s c fs, inv0 E s c fs → Ctx E s c fs → WrAt s (DE).ar.ctrLoc →
    ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
    CtrRow (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1) (DE).L0 (DE).ls0 fs')
      (fun s' c'' => PendA wakeSrc (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1) (DE).L0 (DE).ls0 s' c'' fs') s c'
  /-- the box's initialising store at `Ctx`'s states writing no counter. -/
  hnew0 : ∀ s c fs, inv0 E s c fs → Ctx E s c fs → ¬ WrAt s (DE).ar.ctrLoc →
    ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
    ∀ L, WrAt s L → ¬ ArenaW (DE).ar (DE).L0 (DE).ls0 c' L →
    NewStM wakeSrc (DE).L0
      (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1) (DE).L0 (DE).ls0 fs')
      s c'
  /-- main's state after the `clone`, from `h1`/`inv1` (`A64WakeWcSeg.hpc_of`'s `hpost`). -/
  hpost : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
    SpawnPrem (QG hp i arch (R1W E) (WakeAssemblyR.μR hp i) M r0 r1) (Ly).Λ SccCertificate.asm E 0 d s th
      stack tls r →
    (wakeS arch).Run s [] s' →
    PreR hp i arch (R1W E) (WakeAssemblyR.μR hp i) M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT
      w1 w2 ty1 r0' X q →
    ∃ c J t, Spike.Lib.A64.Flow.WakeWc.ClonePost (Ly) (endR hp i) J t th.st c
  /-- the clone's facts at `PreJAH`'s witnesses (`WakeHPre.hpre_of`'s `hCl`). -/
  hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
    SpawnPrem (QG hp i arch (R1W E) (WakeAssemblyR.μR hp i) M r0 r1) (Ly).Λ SccCertificate.asm E 0 d s th
      stack tls r →
    d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
    I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
    HeldOk2 (Ly).Λ (DE).r0 (DE).r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
    ∃ (X : State → Prop) (q : Spike.Lib.A64.Rt.TcbGG),
      Spike.Lib.WakePreA.ClonePre Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM (Ly).Λ (DE).r0
        (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) X lbl d s ∧
      (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = endR hp i ∧ st.decls = {}) ∧
      (∀ st, X st → st.st.2 = Spike.Lib.WakePreA.cloneAt Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM (Ly).exe ∧
        (st.st.1.regs.getXReg .X3).toBitVec = Spike.Lib.A64.Rt.tcbOf (Ly).lab q) ∧
      Spike.Lib.WakeTcbArea.Q2 q ∧ th0.stack = [] ∧
      (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
        0 < lsize l) ∧
      BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64 = (Ly).pinA + 24#64

/-- **wake.w's AArch64 statement at `D := wakeD`** (see the module doc). -/
theorem wake_finalCA_genW {arch : WeakMem.Arch} {B : Budget} {r0 r1 : ιR hp i → Range}
    /- the loader's parses of the certificate -/
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hnz : WakeOInit.NtZ Λ0 o = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- OPEN: the pre-spawn premises at `DW` -/
    (hO : ∀ E : Entry, E.Ok (Ly).Λ → OpenW hp i cT ls0 Ctx frM inv0 inv1 arch (WakeAssemblyR.MR hp i hpa) r0 r1 E)
    /- the root's choices: the pre-spawn `cT` a dummy heap word (`WakeHG`), the
    record's ranges the data's -/
    (hcT : ∀ E, cT E = WakeHG.cTW hp i) (hr0 : ∀ w, r0 w = WakeOSide.r0W hp i)
    (hr1 : ∀ w, r1 w = WakeOSide.r1W hp i) :
    CorrectE 2 (wakeS arch) (Ly).Λ B SccCertificate.asm :=
  WakeFinalCAO.wake_finalCA_genO hp i (Ab := WakeOD.AbW hp i) (Ac := WakeOD.AcW hp i)
    (D := DW hp i cT ls0 Ctx frM inv0 inv1) hpa hwp hd hlo hpin2 hinit2 hwide
    (fun E hE => match hO E hE with
      | ⟨h1, h0, h1t, h1o, hst, hctr0, hnew0, _, _⟩ =>
        WakeOPremI.oPrem_WI hp i arch E (cT E) (ls0 E) (Ctx E) (frM E) (inv0 E) (inv1 E) hpa hwp hd hlo
          hstat hpin2 hsub1 hc hnz hE.1 hB h1 h0 h1t h1o hst hctr0 hnew0)
    (fun E hE => Spike.Lib.WakeHPre.hpre_of hp i (D := DE) (fun _ _ h => h.1) hr0 hr1
      (fun _ _ _ _ _ _ _ _ _ T S pT cw _ _ _ _ _ _ _ _ hm =>
        WakeHG.memInv_gW hp i hpin2 _ (by rw [← hcT E]; exact hm))
      (hO E hE).hCl)
    (fun E hE => Spike.Lib.A64.Flow.WakeWc.hpc_of hp i (hO E hE).hpost)

/-- **`wake_finalCA_genW` at the certificate's output** `o := outLit`, its
three parses from the single loader check `hP` (`WakeSpawnRP.parsed_outLit`). -/
theorem wake_finalCA_genWP (hp : PlaceW pcfg Λ0 SccCertificate.outLit)
    {arch : WeakMem.Arch} {B : Budget} {r0 r1 : ιR hp i → Range}
    /- the loader's check of the certificate (the trust boundary) -/
    (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ SccCertificate.outLit)
    (hnz : WakeOInit.NtZ Λ0 SccCertificate.outLit = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- OPEN: the pre-spawn premises at `DW` -/
    (hO : ∀ E : Entry, E.Ok (Ly).Λ → OpenW hp i cT ls0 Ctx frM inv0 inv1 arch
      (WakeAssemblyR.MR hp i (WakeSpawnRP.parsed_outLit hP).1) r0 r1 E)
    /- the root's choices -/
    (hcT : ∀ E, cT E = WakeHG.cTW hp i) (hr0 : ∀ w, r0 w = WakeOSide.r0W hp i)
    (hr1 : ∀ w, r1 w = WakeOSide.r1W hp i) :
    CorrectE 2 (wakeS arch) (Ly).Λ B SccCertificate.asm :=
  wake_finalCA_genW hp i cT ls0 Ctx frM inv0 inv1 (WakeSpawnRP.parsed_outLit hP).1
    (WakeSpawnRP.parsed_outLit hP).2.1 (WakeSpawnRP.parsed_outLit hP).2.2 hlo hstat hpin2 hinit2 hwide hsub1 hc hnz hB
    hO hcT hr0 hr1

/-! ## The root's immediate table -/

/-- **The root's immediate table** at the placement input `Λ0`. -/
noncomputable abbrev iW (Λ0 : Scc.Sem.Layout) : CoreTerm.Expr → String → Nat → Option Nat :=
  WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

/-- **`wakeImms` has no entry at the start's `me`**: `iW` overrides nothing. -/
theorem wakeImms_startT : SccCode.wakeImms WakeImmsW.startT "me" 0 = none := by
  simp [SccCode.wakeImms, WakeImmsW.startT, SccCode.wakeImm_t1, SccCode.wakeImm_t0]

/-- **`wakeImms` has no entry at the box's `me`**: `iW` overrides nothing there either. -/
theorem wakeImms_t1_me : SccCode.wakeImms SccCode.wakeImm_t1 "me" 0 = none := by
  simp [SccCode.wakeImms]

/-- `iW`'s `me` at the box's term: main's TCB. -/
theorem iW_imms_c0W_me (Λ0 : Scc.Sem.Layout) : iW Λ0 SccCode.wakeImm_t1 "me" 0 = some (WakeLoadT.tcb0 Λ0) :=
  WakeImmsC0.immsW2_c0 Λ0 _

/-- `iW`'s `z` at the box's term: the certificate's `0`. -/
theorem iW_imms_c0W_z (Λ0 : Scc.Sem.Layout) : iW Λ0 SccCode.wakeImm_t1 "z" 0 = some 0 := by
  rw [iW, WakeImmsC0.immsW2_of_ne (by simp [WakeImmsC0.t1_ne_startT]) (by simp)]; simp [SccCode.wakeImms]

/-- The canonical link layout of wake's certificate (`WakeFinalCAO`'s sanity check). -/
abbrev Λc : Scc.Sem.Layout := (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ

/-- **The root at `i := iW`**: `wake_finalCA_genWP` elaborates at the
canonical layout with the root's immediate table, the dummy heap word as
`cT` and the data's constant ranges (`hcT`, `hr0`, `hr1` by `rfl`). -/
example (arch : WeakMem.Arch) (B : Budget) :=
  wake_finalCA_genWP (hp := WakeFinalCAO.placeW_cert) (i := iW Λc) (arch := arch) (B := B)
    (cT := fun _ => WakeHG.cTW WakeFinalCAO.placeW_cert (iW Λc))
    (r0 := fun _ => WakeOSide.r0W WakeFinalCAO.placeW_cert (iW Λc))
    (r1 := fun _ => WakeOSide.r1W WakeFinalCAO.placeW_cert (iW Λc))
    (hcT := fun _ => rfl) (hr0 := fun _ => rfl) (hr1 := fun _ => rfl)

/-- At the canonical layout with `i := iW`, the start's control is placed at `L0T`. -/
example (s : State) :
    let Λ := (RuntimeLayout.ofPlaceW WakeFinalCAO.placeW_cert (iW Λc)).Λ
    PlacedSE Λ (WakeLoadT.L0T Λ) s ⟨WakePreAsm.wakeTh0.term, WakePreAsm.wakeTh0.env, none⟩ [] :=
  WakeImmsC0.placedSE_start2W WakeFinalCAO.placeW_cert s

/-- At the canonical layout with `i := iW`, main's control at the box is placed at `L0T`. -/
example (s : State) :
    let Λ := (RuntimeLayout.ofPlaceW WakeFinalCAO.placeW_cert (iW Λc)).Λ
    PlacedSE Λ (WakeLoadT.L0T Λ) s WakeC0.c0W [] :=
  WakeImmsC0.placedSE_c0WW WakeFinalCAO.placeW_cert s

section Indep

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i i' : CoreTerm.Expr → String → Nat → Option Nat)

/-- `hpin2` does not read the immediate table. -/
example : ((RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size) =
    ((RuntimeLayout.ofPlaceW hp i').pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i').Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i').Λ.pinned.size) := rfl

/-- `hinit2` does not read the immediate table. -/
example : ((Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0) =
    ((Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i').Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i'), 8⟩ = 0) := rfl

/-- `hwide` does not read the immediate table. -/
example : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe =
    Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i').exe := rfl

/-- `hsub1` does not read the immediate table. -/
example : (WakeOSide.r1W hp i).Sub (RuntimeLayout.ofPlaceW hp i).Λ.stackPool =
    (WakeOSide.r1W hp i').Sub (RuntimeLayout.ofPlaceW hp i').Λ.stackPool := rfl

end Indep

end Spike.Lib.WakeFinalCAW

/-- info: 'Spike.Lib.WakeFinalCAW.wake_finalCA_genW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAW.wake_finalCA_genW

/-- info: 'Spike.Lib.WakeFinalCAW.wake_finalCA_genWP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAW.wake_finalCA_genWP

/-- info: 'Spike.Lib.WakeFinalCAW.wakeImms_startT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAW.wakeImms_startT

/-- info: 'Spike.Lib.WakeFinalCAW.iW_imms_c0W_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAW.iW_imms_c0W_z
