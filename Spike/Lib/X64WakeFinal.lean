/-
**wake.w's x86-64 statement at `D := wakeD`, at the certificate's output**
(draft; the twin of `Spike/Lib/WakeFinalCAO.lean`'s `wake_finalCA_genOP`
and `Spike/Lib/WakeFinalCAW.lean`'s `wake_finalCA_genWP`):
`X64WakeA64.wake_correctE` at every admissible entry from
`X64WakeSpawnRP.wake_obligations_RSP` at `o := outLit`, `asm := certAsm`,
with
- `O` by `X64WakeO.wake_O_at` at `X64.WakeOPremW.oPrem_W` (the parses from
  `hP`, the budget `hB`), at `wakeD` with the levels `W0W`, `W1W` and `h1`'s
  invariant `X64.WakeH1Inv.inv1W` (so `h1`, `h1t`, `h1o` are
  `h1_of`, `h1Take_of`, `h1TakeOwn_of`; `hdt` is `X64.WakeWf.hdtW`);
- `hpre` by `X64WakeHPreC.hpre_ofC` (`hR1` the identity, the record's
  ranges the data's `r0W`/`r1W` by `rfl`, `hown` at `ntA`, `hcl0` by
  `hcl0_W` from `h0`, `hcl_c` by `hcl_c_W`, `hme`, `har` by `hme_W`,
  `har_W`);
- `hMainR` by `X64WakeMainHRI.hMainR_I` (its `hw` by
  `X64WakeHwW.hwide_W`, its `hpv` by `X64WakePrivR.priv_of_R1`);
- the relation `R1X ∧ VPriv` (`X64WakePrivR.Pre1T.priv` of `O`, the cells'
  fragment by `X64WakeWide.hwide_of_placeOKAt`), so `hR1` is `.1`.

- `wake_correctAt`: `Correct` at one entry from `WakeObligations` there
  (`X64WakeA64.wake_correctE`'s proof at `E`, the relation per entry).
- `DX`: the pre-spawn data at an entry.
- `H0X`: `h0`'s statement at `DX`.
- `OpenX`: the premises left open, per entry.
- `wake_finalX_WP`: `CorrectE 2 (wakeS arch) Λ B certAsm`.
- `msBotX`, `inv0G`, `h0_G`: `h0` holds at the greatest closed invariant
  inside `W0W` (`X64GfpS`), as AArch64's `WakeRoot.inv0R`.
- `wake_finalX_G`: `wake_finalX_WP` at `inv0G`, `h0` supplied.
- `HCtrX`, `HNewX`: `hctr0`'s and `hnew0`'s statements at `DX`.
- `hctr0_L`, `hnew0_L`, `wake_finalX_L`: at the root's context (`cT :=
  cTW`, `Ctx := Land.CtxR` at the start control `c0`), `hctr0`/`hnew0` by
  `Land.hctr0_R`/`hnew0_R` (the program by `X64WakeParse.outLit_prog`);
  their `hland`/`hland1` stay open.

**Trust premises**: `hP` (the loader's check of `certAsm` against `outLit`)
and `hB` (the budget's cells). **Instance facts** (decided at the linked
layout): `hlo`, `hA13`, `hpin2`, `hinit2`, `hsub1`, `hc`. **Closed** at
any `PlaceWX` output: `hwide` (`X64WakeHwW.hwide_W`).
**Derived** from the `OPrem` the rows build: main's `ClonePost` at the clone
(`hpost`, `X64WakeHClW.hpostC_W`), its frame pointer at `MainSeg` (`hfp`,
`X64WakeHfp.hfp_W`) and `R1`'s private memory (`hpv`,
`X64WakePrivR.priv_of_R1` at the relation's `VPriv` conjunct). **Closed** at the program: the park's code facts
(`hpcode`, `hpentry`; `X64.Wake.LoopCode.hpcode_W`/`hpentry_W` at
`X64WakeParse.outLit_prog`).
**Open** (`OpenX`, per entry):
- the start's landing: `h0` (the segment before the allocation; its take
  facts `h0t`, `h0o` follow, `X64.WakeWf.h0Take_of`/`h0TakeOwn_of`),
  `hctr0` (the counter's row), `hnew0` (the box's store);
- the load and the clone invariant: `hinit` (the load's relation), `hG`
  (`hpre_of`'s guarantee), `hCl` (the clone's facts without `PreR.hcm`);

**Unlike AArch64**: the text is `certAsm` (with GNU `as`'s sizes and label
offsets; four parses from `hP`, `X64WakeParse.parsed_outLit`); `RSP` has
the instance fact `hA13`; `HMainR` is `hMainR_I`'s (the x64 `MainPieces`,
`hpost`/`hfp` at `Ctl.of s0`, the park's code facts) rather than
`hpc_of`; `PreR` has `hcm`, closed at `wakeD` (`X64WakeHPreC`); `hwide`
is not an instance premise (`hwide_W`); `inv1` is fixed to
`inv1W` (`hcl_c_W` reads its clone clause).
-/
import Spike.Lib.X64WakeSpawnRP
import Spike.Lib.X64WakeHPreC
import Spike.Lib.X64WakeMainHRI
import Spike.Lib.X64WakeLand
import Spike.Lib.X64WakeHfp
import Spike.Lib.X64WakeLoopCode
import Spike.Lib.X64WakePrivR
import Spike.Lib.X64WakeHwW
import Spike.Lib.X64WakeWide

namespace Spike.Lib.X64WakeFinal

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakeSpawnR
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakeParse (certAsm parsed_outLit)
open Spike.Lib.X64.WakeOPremW (W0W W1W)
open Spike.Lib.X64.WakeH1Inv (inv1W)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64WakeTcbArea (Q2)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64WakeInst (wakeG')
open Spike.Lib.X64WakeOkW (recW)
open Spike.Lib.X64WakeMainHR (RW)
open SccCertificate (outLit)

open Spike.Lib.TwoSlot Spike.Lib.Handover Spike.Lib.X64TwoSlot in
/-- **wake.w is correct on x86-64 with two slots at one entry state**,
given the obligations there (`X64WakeA64.wake_correctE`'s proof at `E`; the
twin of `WakeFinalCA.wake_correctAt`): the relation `Q` may depend on `E`. -/
theorem wake_correctAt {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel}
    {E : Entry} {Ti : Cfg → List Ev → Prop} (O : WakeObligations arch Λ B asm Q E Ti) :
    Correct (target (kernel 2) E) (wakeS arch) Λ B asm := by
  have hsim := wake_stepSim O
  refine correct_of_stepSim hsim O.hwf ?_ ?_ ?_ ?_
  · obtain ⟨d, hd⟩ := O.hstart
    obtain ⟨u, hu, -⟩ := load_one hd
    exact ⟨_, hu⟩
  · intro t0 tr t h0 hr
    obtain ⟨s, -, hri, hR⟩ := hsim.reach h0 hr
    rcases hR with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, hca⟩
    · exact O.pre_progress d u s hR hu hpl hn
    · exact O.post_progress t s hP hri hca
  · intro t0 tr t tid es t' k s h0 hr hreach hR hs hk
    change (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' at hs
    have hTi : Ti t tr := by
      obtain ⟨s0, -, hR0⟩ := hsim.init t0 h0
      simpa using wake_tiRun O hr hR0 (O.ti_load t0 h0)
    rcases hR.2 with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩
    · obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨rfl, -⟩⟩ := step_up_cases hn hs
      · exact O.pre_abort tr d u s tid es d' k hreach hR hu hpl hn hTi hd' hk
      · cases hk
    · exact O.post_abort tr t s tid es t' k hreach hP hTi hs hk
  · intro t s hR
    rcases hR with ⟨hri, ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩⟩
    · exact O.pre_wit d u s hR hu hpl hn
    · exact O.post_wit t s hP hri

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 outLit) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (cT : Entry → Loc) (ls0 : Entry → Lsize) (Ctx : Entry → FragS isa)
  (frM : Entry → TermRun.Frame) (inv0 : Entry → FragS isa)

/-- **wake's pre-spawn data at entry `E`**: `wakeD` at the levels `W0W`,
`W1W`, the write tail `DtW` and `h1`'s invariant `inv1W`. -/
abbrev DX (E : Entry) : X64WakeO.OData :=
  X64.WakeOD.wakeD hp i E (cT E) DtW (ls0 E) (W0W certAsm hp i E DtW (Ctx E) (ls0 E) (frM E)) (inv0 E)
    (W1W certAsm hp i E DtW (Ctx E) (ls0 E)) (inv1W certAsm hp i E (cT E) DtW (Ctx E) (ls0 E))

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `DX` at the entry `E`. -/
local notation "DE" => DX hp i cT ls0 Ctx frM inv0 E

set_option hygiene false in
/-- The entry's marks. -/
local notation "μE" => (target (kernel 2) E).marks certAsm (Ly).Λ

set_option hygiene false in
/-- The pre-spawn relation at `DX`, with the private-memory invariant
(`X64WakePrivR.VPriv`). -/
local notation "R1X" => fun d s => X64WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks certAsm (Ly).Λ)
  (DX hp i cT ls0 Ctx frM inv0 E) d s ∧ X64WakePrivR.VPriv (Ly).Λ E d

set_option hygiene false in
/-- The record's main side at the certificate. -/
local notation "MX" => X64WakeAssemblyR.MR hp i certAsm (parsed_outLit hP).1

set_option hygiene false in
/-- The record's ranges: the data's. -/
local notation "r0X" => fun (_ : ιR hp i) => X64WakeOSide.r0W hp i

set_option hygiene false in
/-- The record's ranges: the data's. -/
local notation "r1X" => fun (_ : ιR hp i) => X64WakeOSide.r1W hp i

/-- **`h0`'s statement at `DX`**: the segment before the allocation, inside
`W0W`, under the take move, at `inv0`. -/
abbrev H0X (E : Entry) : Prop :=
  SegInvS (DE).W0 (TakeCKS (DE).a (DE).Cl) wakeSrc (DE).L0
    (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1)
      (DE).L0 (DE).ls0) (DE).inv0

/-- **`hctr0`'s statement at `DX`**: the counter's row after a counter add
from `inv0` under `Ctx`. -/
abbrev HCtrX (E : Entry) : Prop :=
  ∀ s c fs, inv0 E s c fs → Ctx E s c fs → WrAt s (DE).ar.ctrLoc →
    ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
    CtrRow
      (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1)
        (DE).L0 (DE).ls0 fs')
      (fun s' c'' => PendA wakeSrc (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1) (DE).L0 (DE).ls0 s' c'' fs')
      s c'

/-- **`hnew0`'s statement at `DX`**: the box's store from `inv0` under
`Ctx`, off the counter and the arena. -/
abbrev HNewX (E : Entry) : Prop :=
  ∀ s c fs, inv0 E s c fs → Ctx E s c fs → ¬ WrAt s (DE).ar.ctrLoc →
    ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
    ∀ L, WrAt s L → ¬ ArenaW (DE).ar (DE).L0 (DE).ls0 c' L →
    NewStM wakeSrc (DE).L0
      (msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1)
        (DE).L0 (DE).ls0 fs')
      s c'

/-- **The premises left open at `DX`**, per entry (grouped in the module
doc). -/
structure OpenX (arch : WeakMem.Arch)
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true) (E : Entry) : Prop where
  /-- The segment before the allocation. -/
  h0 : H0X hp i cT ls0 Ctx frM inv0 E
  /-- The counter's row. -/
  hctr0 : HCtrX hp i cT ls0 Ctx frM inv0 E
  /-- The box's store. -/
  hnew0 : HNewX hp i cT ls0 Ctx frM inv0 E
  /-- The load's relation. -/
  hinit : ∀ d : Cfg, (target (kernel 1) E).load certAsm (Ly).Λ = some d →
    ∃ s0, (wakeS arch).init s0 ∧
      RSAH (Ly).Λ (srcPo 2 arch wakeSrc) wakeSrc (DE).G (DE).own (I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1)
        (HeldOk2 (Ly).Λ (DE).r0 (DE).r1) μE (DE).ar d s0
  /-- The data's guarantee below the clone's record's. -/
  hG : ∀ d s (th : Thread isa) (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) ts hd l T S pT cw,
    R1X d s → d.1.threads = #[th] → s.ths = #[th0] →
    I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
    TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
    Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem → ∀ X, ClonePre (Ly).Λ (DE).r0 (r1Of (Ly).lab) X lbl d s →
    MemInv (DE).G d.1.mem → MemInv (wakeG' hp i (recW T S lbl lsize l pT cw)) d.1.mem
  /-- The clone's facts at `PreJAH`'s witnesses (without `PreR.hcm`). -/
  hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hd : Option (Nat × TermRun.Word)),
    SpawnPrem (QG hp i arch R1X (X64WakeAssemblyR.μR hp i certAsm) MX r0X r1X) (Ly).Λ certAsm E 0 d s th
      stack tls r →
    d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
    I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
    HeldOk2 (Ly).Λ (DE).r0 (DE).r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
    ∃ (X : State → Prop) (q : TcbGG), ClonePre (Ly).Λ (DE).r0 (r1Of (Ly).lab) X lbl d s ∧
      (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = X64WakeAssemblyR.endR hp i ∧ st.decls = {}) ∧
      (∀ st, X st → st.st.2 = cloneAt (Ly).exe ∧ st.st.1.regs.get64 .r8 = tcbOf (Ly).lab q) ∧
      Q2 q ∧ th0.stack = [] ∧
      (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
        0 < lsize l)

/-- **wake.w's x86-64 statement at the certificate's output** (see the
module doc). -/
theorem wake_finalX_WP {arch : WeakMem.Arch} {B : Budget}
    /- the loader's check of the certificate (the trust boundary) and the budget -/
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    /- OPEN: per entry -/
    (hO : ∀ E : Entry, E.Ok (Ly).Λ → OpenX hp i cT ls0 Ctx frM inv0 arch hP E) :
    CorrectE 2 (wakeS arch) (Ly).Λ B certAsm := by
  intro E hE
  have h := hO E hE
  have hpa := parsed_outLit hP
  have hOP := X64.WakeOPremW.oPrem_W certAsm hp i arch E (cT E) DtW (ls0 E) (Ctx E) (frM E) (inv0 E)
    (inv1W certAsm hp i E (cT E) DtW (Ctx E) (ls0 E)) hpa.1 hpa.2.1 hpa.2.2.1 hlo hpin2 hsub1 hc hB
    (fun l b n h1 h2 => X64.WakeH1Inv.h1_of certAsm hp i E (cT E) DtW (Ctx E) (ls0 E) _ (inv0 E) l b n h1 h2)
    h.h0 (Spike.Lib.X64.WakeWf.h0Take_of h.h0) (Spike.Lib.X64.WakeWf.h0TakeOwn_of h.h0)
    (X64.WakeH1Inv.h1Take_of certAsm hp i E (cT E) DtW (Ctx E) (ls0 E))
    (X64.WakeH1Inv.h1TakeOwn_of certAsm hp i E (cT E) DtW (Ctx E) (ls0 E))
    h.hctr0 h.hnew0 X64.WakeWf.hdtW h.hinit
  exact wake_correctAt <| X64WakeSpawnRP.wake_obligations_RSP hp i hP (r0 := r0X) (r1 := r1X) hE.1
    (X64WakePrivR.Pre1T.priv (X64WakeO.wake_O_at hOP) (X64WakeWide.hwide_of_placeOKAt hp hpa.1))
    hlo hA13 hpin2 hinit2 (X64WakeHwW.hwide_W hp i)
    (X64WakeHPreC.hpre_ofC hp i (D := DE) (fun _ _ h => h.1) hpin2 (fun _ => rfl) (fun _ => rfl)
      ⟨_, fun _ _ => rfl⟩ h.hG h.hCl (X64WakeHPreC.hcl0_W hp i h.h0) (X64WakeHPreC.hcl_c_W hp i)
      (X64WakeHPreC.hme_W hp i) (X64WakeHPreC.har_W hp i))
    (X64WakeMainHRI.hMainR_I hp i (X64WakeHwW.hwide_W hp i) (fun _ _ h => X64WakePrivR.priv_of_R1 h)
      (X64WakeHClW.hpostC_W hp i (cT E) DtW (ls0 E) (Ctx E) (frM E) (inv0 E) (fun _ _ h => h.1) hOP)
      (X64WakeHfp.hfp_W hp i (cT E) DtW (ls0 E) (Ctx E) (frM E) (inv0 E) (fun _ _ h => h.1) hOP)
      (X64.Wake.LoopCode.hpcode_W hp i X64WakeParse.outLit_prog ⟨.ret (.var "x"), default, none⟩)
      (X64.Wake.LoopCode.hpentry_W hp i X64WakeParse.outLit_prog))
    (Ab := X64.WakeOD.AbW hp i) (Ac := X64.WakeOD.AcW hp i)

set_option hygiene false in
/-- `DX` with no pre-allocation invariant (`W0`, the memory side's other
fields and `inv1` do not read it). -/
local notation "DB" => DX hp i cT ls0 Ctx frM (fun _ _ _ _ => False) E

/-- **`h0`'s memory side with no pre-allocation fragment** at entry `E`:
`DX`'s, with `I2`'s `inv0` disjunct `⊥` (an allocation only reaches
`inv1W`). -/
abbrev msBotX (E : Entry) (fs : List TermRun.Frame) : MemSide isa :=
  msOfA (Ly).Λ μE (DB).rd (DB).G (DB).own (DB).ar (I2 (DB).ar (DB).L0 (DB).ls0 (fun _ _ _ => False) (DB).inv1)
    (DB).L0 (DB).ls0 fs

/-- **`h0`'s invariant at entry `E`**: the greatest closed invariant inside
`W0W` under the take move at `msBotX` (`X64GfpS.GfpS`). -/
abbrev inv0G (E : Entry) : FragS isa :=
  X64GfpS.GfpS (DB).W0 (TakeCKS (DB).a (DB).Cl) wakeSrc (DB).L0 (msBotX hp i cT ls0 Ctx frM E)

/-- **`h0` at `inv0G`**: `GfpS` is a segment (`segInvS_gfpS`), lifted from
`msBotX` to `I2 inv0G` (`segInvS_mono_xa`). -/
theorem h0_G (E : Entry) : H0X hp i cT ls0 Ctx frM (inv0G hp i cT ls0 Ctx frM) E :=
  X64GfpS.segInvS_mono_xa X64GfpS.segInvS_gfpS (fun fs => X64GfpS.msOfA_with_xa fs) fun fs _ _ _ _ _ h =>
    X64GfpS.msOfA_xa_mono (fun _ _ _ _ _ hI => hI.elim (fun hF => hF.2.2.elim) .inr) fs h

/-- **`wake_finalX_WP` at `h0`'s greatest invariant** (`inv0 := inv0G`):
`h0` is supplied (`h0_G`), so `OpenX` is owed given it. -/
theorem wake_finalX_G {arch : WeakMem.Arch} {B : Budget}
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    (hO : ∀ E : Entry, E.Ok (Ly).Λ → H0X hp i cT ls0 Ctx frM (inv0G hp i cT ls0 Ctx frM) E →
      OpenX hp i cT ls0 Ctx frM (inv0G hp i cT ls0 Ctx frM) arch hP E) :
    CorrectE 2 (wakeS arch) (Ly).Λ B certAsm :=
  wake_finalX_WP hp i cT ls0 Ctx frM _ hP hB hlo hA13 hpin2 hinit2 hsub1 hc
    fun E hE => hO E hE (h0_G hp i cT ls0 Ctx frM E)

/-! ## At the root's context -/

set_option hygiene false in
/-- The root's `cT`: the dummy heap word. -/
local notation "cTR" => fun _ : Entry => X64WakeHG.cTW hp i

set_option hygiene false in
/-- The root's context at the start control `c0`. -/
local notation "CtxL" => fun E : Entry =>
  X64.WakePh.Land.CtxR (Ly) c0 (X64.WakePh.Land.refW certAsm hp i ls0 E)

/-- **`hctr0` at the root's context** (`Land.hctr0_R`), given its tail
`HLand` at `inv0G`; the program by `X64WakeParse.outLit_prog`. -/
theorem hctr0_L (c0 : Ctl) (hc : Spike.Lib.X64.Rt.CtrZ outLit) (E : Entry)
    (hland : X64.WakePh.Land.HLand certAsm hp i c0 ls0 (inv0G hp i cTR ls0 CtxL frM E) E) :
    HCtrX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E :=
  X64.WakePh.Land.hctr0_R (hp := hp) (i := i) X64WakeParse.outLit_prog hc E hland

/-- **`hnew0` at the root's context** (`Land.hnew0_R`), given the box
store's landing `hland1` in `I2`'s fragment. -/
theorem hnew0_L (c0 : Ctl) (E : Entry)
    (hland1 : ∀ Lnd, X64.WakePh.Land.GsW (Ly) c0 (X64.WakePh.Land.refW certAsm hp i ls0 E) Lnd →
      ∀ l A s' c', Spike.Lib.X64WakeLoadT.L0T (Ly).Λ l = none → Lnd l A 1 s' c' →
      (msOfA (Ly).Λ μE (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).rd
        (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).G
        (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).own
        (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).ar
        (I2 (X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T (ls0 E))
          (inv0G hp i cTR ls0 CtxL frM E) (inv1W certAsm hp i E (X64WakeHG.cTW hp i) DtW (CtxL E) (ls0 E)))
        (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T (ls0 E)) []).xa l A 1 s' c') :
    HNewX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E :=
  X64.WakePh.Land.hnew0_R (hp := hp) (i := i) X64WakeParse.outLit_prog E hland1

/-- **wake.w's x86-64 statement at the root's context** (`cT := cTW`,
`Ctx := Land.CtxR` at the start control `c0`, `inv0 := inv0G`): `h0` by
`h0_G`, `hctr0`/`hnew0` by `Land.hctr0_R`/`hnew0_R`, whose premises
`hland` (the counter add's tail in `inv0G`) and `hland1` (the box store's
landing in `I2`'s fragment) stay open, per entry. -/
theorem wake_finalX_L {arch : WeakMem.Arch} {B : Budget} (c0 : Ctl)
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    /- OPEN: the counter add's tail and the box store's landing, per entry -/
    (hland : ∀ E : Entry, E.Ok (Ly).Λ →
      X64.WakePh.Land.HLand certAsm hp i c0 ls0 (inv0G hp i cTR ls0 CtxL frM E) E)
    (hland1 : ∀ E : Entry, E.Ok (Ly).Λ →
      ∀ Lnd, X64.WakePh.Land.GsW (Ly) c0 (X64.WakePh.Land.refW certAsm hp i ls0 E) Lnd →
      ∀ l A s' c', Spike.Lib.X64WakeLoadT.L0T (Ly).Λ l = none → Lnd l A 1 s' c' →
      (msOfA (Ly).Λ μE (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).rd
        (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).G
        (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).own
        (DX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E).ar
        (I2 (X64.WakeOD.arW hp i) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T (ls0 E))
          (inv0G hp i cTR ls0 CtxL frM E) (inv1W certAsm hp i E (X64WakeHG.cTW hp i) DtW (CtxL E) (ls0 E)))
        (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T (ls0 E)) []).xa l A 1 s' c')
    /- OPEN: the rest of `OpenX`, given `h0`, `hctr0`, `hnew0` -/
    (hO : ∀ E : Entry, E.Ok (Ly).Λ → H0X hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E →
      HCtrX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E →
      HNewX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) E →
      OpenX hp i cTR ls0 CtxL frM (inv0G hp i cTR ls0 CtxL frM) arch hP E) :
    CorrectE 2 (wakeS arch) (Ly).Λ B certAsm :=
  wake_finalX_G hp i cTR ls0 CtxL frM hP hB hlo hA13 hpin2 hinit2 hsub1 hc fun E hE h0 =>
    hO E hE h0 (hctr0_L hp i ls0 frM c0 hc E (hland E hE)) (hnew0_L hp i ls0 frM c0 E (hland1 E hE))

end Spike.Lib.X64WakeFinal

/-- info: 'Spike.Lib.X64WakeFinal.wake_correctAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.wake_correctAt

/-- info: 'Spike.Lib.X64WakeFinal.wake_finalX_WP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.wake_finalX_WP

/-- info: 'Spike.Lib.X64WakeFinal.h0_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.h0_G

/-- info: 'Spike.Lib.X64WakeFinal.wake_finalX_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.wake_finalX_G

/-- info: 'Spike.Lib.X64WakeFinal.hctr0_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.hctr0_L

/-- info: 'Spike.Lib.X64WakeFinal.hnew0_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.hnew0_L

/-- info: 'Spike.Lib.X64WakeFinal.wake_finalX_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeFinal.wake_finalX_L
