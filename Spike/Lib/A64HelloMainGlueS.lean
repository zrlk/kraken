/-
**`hello.w`'s `scc_rt_main` from its entry to `wc_main`'s heap abort at depth** (AArch64,
Option A, step 4a): `MainGlueW.main_wc_segW` and the `scc_rt_main` part of
`MainGlueW.hello_start_wc_segW` over segments with frames (`SegWS`, `Spike/Lib/SegS.lean`), `wc_rodata` under
the frame `fr` its source call pushed (at the real run `HelloRdCf.frH env`). The twin at hello of
`Hello1.hello1_setup_main_segWS` (`Spike/Lib/A64Hello1SetupGlue.lean`).

`MainGlueW` runs `scc_rt_main` as one frameless segment, so at the real run (the setup start, `rodata`
called) its `hedge` and its `rodata` call hold vacuously. Here `scc_rt_main` up to `bl wc_rodata` is at `[]`,
`wc_rodata` (call taken at its entry, return popped at `.sp0`) at `[fr]`, and `scc_rt_main`'s rest with
`wc_main` at `[]` again (`HelloM.hello_main_pre_segWS`, `HelloM.hello_main_post_segWS`).

- `SegWS.seq_or`: a segment, then another from one of its exits (`Hello1.SegWS.seq_or`, restated here to keep
  the hello1 start out of the imports).
- `MainWcPS`: `MainGlueW.MainWcP` with frames: `wc_rodata`'s premises at `[fr]` (`hW : MainPostSWH`, `h1`,
  `h3`, `hfen` under `ms [fr]`, `hedge` into `retJH fr Jr`), `wc_main`'s at `[]` under `ms []`.
- `main_wc_segWS`: from `wc_rodata`'s `.sp0` at `[fr]` to `wc_main`'s abort exit at `[]`.
- `hello_main_wc_segWS`: from `scc_rt_main`'s entry at `[]` to `wc_main`'s abort exit at `[]` or
  `wc_rodata`'s heap abort at `[fr]`.
-/
import Spike.Lib.A64HelloMainPreS
import Spike.Lib.A64HelloMainPostS
import Spike.Lib.A64HelloWcEntry
import Spike.Lib.A64HelloMainPostT

namespace Spike.Lib.A64.HelloPh.MainGlueS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (abi)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib (FragS Frag MemSide Region SegW SegWS LocalRun XchgSite FenceRun FrameRun)
open Spike.Lib.A64.Flow (FStable rAddr tcbA NoMsrW At ProW BlkW CKept)
open Spike.Lib.A64.Flow.Ret0 (LimOk)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mN0 mNC rpK1 rpK2 aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN RdPreW)
open Spike.Lib.A64.Flow.HelloM (MainPostSWH wcR wcF wcJ0 JrT)
open Spike.Lib.A64.Flow.HelloWc (wXH bXH WcPreWH WcSp0WH)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW tpG)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.HelloRdCf (retJH)
/-- `Flow`'s abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## Sequencing into one exit -/

namespace SegWS

variable {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide I} {P Q₁ Q₂ R : FragS I}

/-- **A segment, then another from one of its exits**: the other exits stay (`Hello1.SegWS.seq_or`). -/
theorem seq_or (h₁ : SegWS W K p lbl ms P (fun s c fs => Q₁ s c fs ∨ Q₂ s c fs)) (h₂ : SegWS W K p lbl ms Q₁ R) :
    SegWS W K p lbl ms P (fun s c fs => R s c fs ∨ Q₂ s c fs) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · obtain ⟨ho, hk⟩ := ho₁ s c fs h
    have hX : ∀ s c fs, (i₁ s c fs ∨ (Q₁ s c fs ∨ Q₂ s c fs)) →
        ((i₁ s c fs ∨ i₂ s c fs) ∨ (R s c fs ∨ Q₂ s c fs)) := fun s c fs h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr (hs₂ s c fs h))
      · exact .inr (.inr h)
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono hX, hk.mono hX⟩
  · obtain ⟨ho, hk⟩ := ho₂ s c fs h
    have hX : ∀ s c fs, (i₂ s c fs ∨ R s c fs) → ((i₁ s c fs ∨ i₂ s c fs) ∨ (R s c fs ∨ Q₂ s c fs)) :=
      fun s c fs h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono hX, hk.mono hX⟩

end SegWS

/-! ## From `wc_rodata`'s `.sp0` under its frame to `wc_main`'s heap abort -/

/-- **`main_wc_segWS`'s premises** past the layout's, for a caller's state `m0`, `σC` at `wc_rodata`'s call
under the frame `fr` and `wc_main`'s region `D` deep at its call (`MainGlueW.MainWcP` with frames):
`wc_rodata`'s states at `[fr]` and the `.sp0` block's at `[]` (`hW`), `wc_rodata`'s source and frame facts from
`.sp0` under `ms [fr]` (`hra` … `hedge`, its source's `ret` popping `fr` into `Jr`: `retJH fr Jr`), and
`wc_main`'s entry's at `[]` under `ms []` (`hJpT` … `hxa`; `wc_main`'s at `JrT Jr t R`, `Jp`'s thread pointer
`t` by `hJpT`). The allocator's words (`hmem0`) are left to the caller. -/
structure MainWcPS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (D : Int)
    (F : MachineData → Prop) (fr : TermRun.Frame) (m0 : MachineData) (σC : FAS)
    (Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop) (t : UInt64) : Prop where
  hW : MainPostSWH W K exe endPc R F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 (JrT Jr t R)
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8))
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
    ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none
  hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c'
  h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
    c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c'
  h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
    c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p (ms [fr]).pub .st c c' ∧ J5 σ0 c'
  hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : FAS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
    σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
    σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
    ∃ c', LocalRun p c c' ∧ retJH fr Jr σ' c'
  hJpT : ∀ σ0 c, Jp σ0 c → σ0.regs.TPIDR_EL0 = t
  hWp : ∀ m1 σ1, WcPreWH (NoMsrW (tpG t fun s c => W s c []) K) K exe endPc (wcR R D) (wcF R D F m1 σ1)
    (tpXa (ms []) t) (wcJ0 (mWC (_root_.Executable.labels exe).label σC (JrT Jr t R)).J σ1)
    (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
  hWs : ∀ m1 σ1, WcSp0WH (NoMsrW (tpG t fun s c => W s c []) K) K exe endPc (wcR R D) (wcF R D F m1 σ1)
    (tpXa (ms []) t) (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
  hlim : ∀ σ c, JrT Jr t R σ c → LimOk (ms []) F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec)
  hloc : ∀ σ c, JrT Jr t R σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c'
  hq : ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
    q.h = 256#64 ∧ q.k = 1#64 ∧ q.u (ms []) = 2#64
  hbox : ∀ q : AGB (ms []) (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → BoxW lbl q.1
  hcell0 : ∀ q : AGB (ms []) (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → ∀ o : Nat,
    (ms []).lo o → o + (ms []).units 1 q.1.τ ≤ (ms []).cells →
    (ms []).mp ⟨BitVec.ofNat 64 ((ms []).heap + 16 * o + (ms []).off 1 q.1.τ), 8⟩ true ∧
    ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ((ms []).heap + 16 * o + (ms []).off 1 q.1.τ)) 8 = none
  hxa : ∀ m1 σ1, ∀ l A s c, lbl l = none → At exe endPc (wcR R D) (wcF R D F m1 σ1)
    (bXH (ms []) (_root_.Executable.labels exe).label
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) l A) s c →
    TP t s → (ms []).xa l A 1 s c

section Main

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` under its frame to `wc_main`'s first allocation's heap abort is
one segment inside `W`** in any valid layout of `helloProg`: `hello_main_post_segWS` (`wc_rodata`'s rest at
`[fr]`, its return popping `fr`, `hfr`) into `wc_main`'s region `D` deep at its call, then at every caller's
state `m1`, `σ1` there `hello_wc_entry_segJr` at `[]`, its allocator's words from `F`'s (`hmem0`). -/
theorem main_wc_segWS (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXH (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) .abort) s c ∧ TP t s) []) :=
  Spike.Lib.A64.Flow.HelloM.hello_main_post_segWST hp hend hK' (by omega) hD16 hF hR hal hlo hloD hhi hfr
    hP.hJpT hP.hW hP.hra hP.hmem hP.hr0 hP.h1 hP.h2 hP.hr2 hP.h3 hP.h4 hP.hfen hP.hedge
    (Q := fun m1 σ1 s c => At exe endPc (wcR R D) (wcF R D F m1 σ1)
      (wXH (ms []) (_root_.Executable.labels exe).label
        (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) .abort) s c ∧ TP t s)
    fun m1 σ1 hR' hal' hF' =>
      Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJr hK hp hend hF' hR' hal' (show -D ≤ -304 by omega)
        (show (0 : Int) ≤ 0 by decide) (fun _ _ h => h.2.1) (hP.hWp m1 σ1) (hP.hWs m1 σ1) hP.hlim hP.hloc hP.hq
        hmem0 hP.hbox hP.hcell0 (hP.hxa m1 σ1)

/-- **`scc_rt_main` from its entry to `wc_main`'s first allocation's heap abort, `wc_rodata` under its
frame**: `hello_main_pre_segWS` at the frames `[fr]` (`hpro` … `hxa`: `scc_rt_main` up to `bl wc_rodata` at
`[]`, the source's call of `rodata` pushing `fr`, `wc_rodata` up to its allocator's return at `[fr]`), the
allocator's return at `.sp0` into `Jp` (`hret`), then `main_wc_segWS` from there (`hP`, `hmem0`). The other
exit is `wc_rodata`'s heap abort at `[fr]`. -/
theorem hello_main_wc_segWS (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = [])
    {J J' : FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hpro : ProW (fun s c => W s c []) K exe endPc R F (ms []) ((_root_.Executable.labels exe).label "scc_rt_main")
      80 8 ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J)
    (hcall : BlkW (fun s c => W s c []) K exe endPc R F (mN0 (_root_.Executable.labels exe).label J)
      Spike.Lib.A64.Flow.Hello1.mB0)
    (hWe : ∀ s c, At exe endPc R F (mNC (_root_.Executable.labels exe).label J) s c → W s c [])
    (hrun : ∀ σ c, (mNC (_root_.Executable.labels exe).label J).J σ c →
      ∃ c', FrameRun p (c, []) (c', [fr]) ∧ J' σ c')
    (hJ' : ∀ σ c', J' σ c' → ∃ c, (mNC (_root_.Executable.labels exe).label J).J σ c)
    (hrd : ∀ m0 σC, RdPreW (fun s c => W s c [fr]) K exe endPc (mR R) (mF R F m0 σC) (ms [fr]) (mRdJ0 J' σC)
      (J1 σC))
    (hlimM : ∀ σ c, J σ c →
      LimOk (ms []) F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk (ms [fr]) F exe endPc (tcbA σ.regs 8)
      (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hloc : ∀ σC σ c, mRdJ0 J' σC σ c → ∃ c', LocalRun p c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK (ms [fr]) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms [fr]) = 3#64)
    (hmem : ∀ q : Call, q.OK (ms [fr]) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms [fr]).ctr ∨
        ∃ o, o + (ms [fr]).units q.n q.τ ≤ (ms [fr]).cells ∧ a.toNat = q.hdrAt (ms [fr]) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ m0 σC, ∀ q : AG (ms [fr]) (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label (mRdJ0 J' σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label (ms [fr]) q.1 .e).J
          (Spike.Lib.A64.Flow.enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms [fr]) q.1 l b w) s c →
        (ms [fr]).xa l b w s c)
    {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : MachineData → FAS → FAS → Ctl → Prop} {t : UInt64}
    (hret : ∀ m0 σC σ c, (rX (ms [fr]) (_root_.Executable.labels exe).label lbl (J1 σC) .sp0).J σ c →
      Jp m0 σC σ c)
    (hP : ∀ m0 σC, MainWcPS W K p lbl ms exe endPc R D F fr m0 σC (Jp m0 σC) (Jp' m0 σC) (Jx1 m0 σC) (J2 m0 σC)
      (J2' m0 σC) (J3 m0 σC) (J4 m0 σC) (J5 m0 σC) (Jr m0 σC) (Jr1 m0 σC) t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩).at [])
      (fun s c fs => Frag.at (fun s c => ∃ m0 σC m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
          (wXH (ms []) (_root_.Executable.labels exe).label
            (wcJ0 (mWC (_root_.Executable.labels exe).label σC (Jr1 m0 σC)).J σ1) .abort) s c ∧ TP t s) [] s c fs ∨
        Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX (ms [fr]) (_root_.Executable.labels exe).label lbl (J1 σC) .abort) s c) [fr] s c fs) := by
  let lab := (_root_.Executable.labels exe).label
  have hA := Spike.Lib.A64.Flow.HelloM.hello_main_pre_segWS (fs1 := [fr]) hp hend hF hR hal hlo hhi hpro hcall
    hWe hrun hJ' hrd hlimM hlimR hloc hq hmem hxa
  have hB : SegWS W K p lbl ms
      (fun s c fs => ∃ m0 σC, (At exe endPc (mR R) (mF R F m0 σC)
        (pN lab (Jp m0 σC) (Jp' m0 σC) (Jx1 m0 σC) (J2 m0 σC) (J2' m0 σC) (J3 m0 σC) (J4 m0 σC) (J5 m0 σC)
          .s0)).at [fr] s c fs)
      (Frag.at (fun s c => ∃ m0 σC m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
          (wXH (ms []) lab (wcJ0 (mWC lab σC (Jr1 m0 σC)).J σ1) .abort) s c ∧ TP t s) []) :=
    SegWS.exists_pre fun m0 => SegWS.exists_pre fun σC =>
      (main_wc_segWS hK hK' hp hend hD hD16 hF hR hal hlo hloD hhi hfr (hP m0 σC) hmem0).mono_post
        fun _ _ _ ⟨⟨m1, σ1, h⟩, e⟩ => ⟨⟨m0, σC, m1, σ1, h⟩, e⟩
  refine SegWS.seq_or (hA.mono_post ?_) hB
  rintro s c fs ⟨⟨m0, σC, y, h⟩, rfl⟩
  cases y
  · obtain ⟨he, hn, hdc, hpc, σ, hA', hD', hJ⟩ := h
    exact .inl ⟨m0, σC, ⟨he, hn, hdc, hpc, σ, hA', hD', hret m0 σC σ c hJ⟩, rfl⟩
  · exact .inr ⟨⟨m0, σC, h⟩, rfl⟩

end Main

end Spike.Lib.A64.HelloPh.MainGlueS

/-- info: 'Spike.Lib.A64.HelloPh.MainGlueS.main_wc_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainGlueS.main_wc_segWS

/--
info: 'Spike.Lib.A64.HelloPh.MainGlueS.hello_main_wc_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainGlueS.hello_main_wc_segWS
