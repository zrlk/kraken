/-
**A covered block of an `Accepted2` body inside `W2`** (x86-64; the twin
of `Spike/Lib/LowerA64/W2Body.lean`): the producer of `BlkW` at `W2`
(`Spike/Lib/LowerX64/SFactsA2.lean`) for a block of the code predicate
(`SubCd (CdC …)`), assembled from its parts (`BlkW.w2`,
`Spike/Lib/LowerX64/W2Blk.lean`):

- the state's facts: `SFacts` at the source start's control from the phase
  check (`blkW_postO'` at `dumN`, `cfacts_c0`);
- the write obligation: a covered block writes nothing (`blkW_noWr'`, the
  stack's cells are private), so `WrOkA` holds (`wrOkA_of_noWr`);
- the placement: `blkW_placedS` (`Spike/Lib/LowerX64/PlacedBlk.lean`) from
  the node's `SlotRepAt`, no slot written before the block's last
  instruction;
- the abort phase `AbSt`: a premise at the phase `Ab` the consumer picks;
- the node's controls: `main`'s `ret` excluded and `FrOk2`.

- `blkW_noWr'`: `blkW_noWr` at a block's code rather than its placement;
- `blkW_noSys'`: a covered block's states off a system call (`W2Part`'s
  `print` output fact vacuous);
- `blkW_w2BP`, `blkW_w2CP`: as `blkW_w2B`, `blkW_w2C` with the placement a premise;
- `blkW_w2BPE`: `blkW_w2BP` with the placement at `PlacedSE`;
- `blkW_w2Pend`: at a checked `+`'s pending store (`blkW_placedS_upd`);
- `nodeW_w2CalleeEntry`: at a callee's entry (its prologue head);
- `slotRepAt_bodyN2`, `slotRepAt_pendN2`: the producers' `hJp` at the body's nodes;
- `blkW_w2B`: the producer at a block's code and phase check;
- `blkW_w2C`: the producer at the code predicate;
- `blkW_w2Call`: the producer at a call's `callq` (`BlC`).
-/
import Spike.Lib.LowerX64.PlacedBlk
import Spike.Lib.LowerX64.Node2
import Spike.Lib.LowerX64.CallBlkW
import Spike.Lib.X64AllocG

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At cellOff okBlk CodeAt FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Scc.Cert.Rt.X64 (blockAt)
open Scc.Emit.X64 (i64 rel)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block's states write nothing** (`blkW_noWr` at the block's
code `hcode`). -/
theorem blkW_noWr' {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) :
    BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c hs hn _ _ _ _ _ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ :=
    Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.X64.classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s hs hn).cell hd rfl rfl rfl
  obtain ⟨m', hex, -⟩ := Spike.Lib.X64.exec_ai haok hR hlo hhi hc hreg hA'
  exact noWr_done hex

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block's states are off a system call** (`blkW_noWr'`'s
cells: no covered instruction is a `syscall`). -/
theorem blkW_noSys' {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c hs hn _ _ _ _ _ k hk m _ _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, -, -⟩ :=
    Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.X64.classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s hs hn).cell hd rfl rfl rfl
  refine Scc.Sem.X64.atSyscall_false_of_cellAt hc fun w w' h => ?_
  cases a <;> (try simp only [Spike.Lib.X64.AI.toDir, op64] at h) <;> (try cases h)
  exact absurd (hreg _ _ rfl) (by simp [Spike.Lib.X64.RegOnly])

variable {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {rs : Scc.IR.Reg → Option Int}
  {B : Nat → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`, its states placed (`hP`): as `blkW_w2B` with the placement a
premise (a pending store's, `blkW_placedS_upd`). -/
theorem blkW_w2BP {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  have hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk :=
    blkW_postO' (n := dumN n) (dead := fun _ => false) (ra := ra) hI hcode hok hR hlo hhi hR8 hl hh
      (fun _ _ h => h.1 ▸ cfacts_c0) hph (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim)
      (fun _ _ _ => rfl) hsub hfit hFO
  have hW : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk :=
    blkW_noWr' hcode hok hR hlo hhi
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.X64.AllocG.BlkW.imp hW (blkW_noSys' hcode hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.X64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2 hp hS ?_ hJ
  exact Spike.Lib.X64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`, its states at `PlacedSE` (`hP`: placed, or the current frame in
the output extern's model): `blkW_w2BP` at `BlkW.w2E`. -/
theorem blkW_w2BPE {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  have hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk :=
    blkW_postO' (n := dumN n) (dead := fun _ => false) (ra := ra) hI hcode hok hR hlo hhi hR8 hl hh
      (fun _ _ h => h.1 ▸ cfacts_c0) hph (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim)
      (fun _ _ _ => rfl) hsub hfit hFO
  have hW : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk :=
    blkW_noWr' hcode hok hR hlo hhi
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.X64.AllocG.BlkW.imp hW (blkW_noSys' hcode hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedSE Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.X64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2E hp hS ?_ hJ
  exact Spike.Lib.X64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`: a block in the code at its node's pc (`hcode`), passing the
phase check there (`hph`), covered at its node's offsets (`hok`), with no
`ret` (`hnr`) and no slot written before its last instruction (`hnw`), its
states in the abort phase's facts (`hab`); at a node whose controls are
placed in the abstract slot file (`hJp`, every slot a cell of the region),
exclude `main`'s `ret` and are free of `ZBad` (`hJ`), the suspended frames
placed under the frame condition (`hfp`). -/
theorem blkW_w2B {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List (Directive × Nat)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) (hnw : noSlotWr blk.dropLast = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  exact blkW_w2BP hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hcode hph hok hnr hab
    (blkW_placedS hFS hJp hrs hfp hnw) hJ

/-- **A covered block of the code without a `ret` is inside `W2`** at the
frames `fs`, its states placed (`hP`): as `blkW_w2C` with the placement a
premise (`blkW_w2BP`). -/
theorem blkW_w2CP {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List (Directive × Nat)}
    (hcd : Spike.Lib.LowerX64.SubCd (CdC cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, off, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
    simp [cellOff]
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hc, ← hpc] at hph
  have hb' := blockAt_sub hb
  have hpc' : lab L + Int64.ofNat (off + (pre.map (·.2)).sum) = n.pc := by
    rw [hpc, ← hpc0, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb'
    rwa [hI.labOk, hpc'] at this
  exact blkW_w2BP hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hcode hph hok hnr hab hP hJ

/-- **A covered block of the code without a `ret` is inside `W2`** at the
frames `fs` (`blkW_w2B`): a block of the code predicate `CdC` at a return
address `ra` (`SubCd`, its phase from the run's check). -/
theorem blkW_w2C {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List (Directive × Nat)}
    (hcd : Spike.Lib.LowerX64.SubCd (CdC cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) (hnw : noSlotWr blk.dropLast = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  exact blkW_w2CP hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hcd hok hnr hab
    (blkW_placedS hFS hJp hrs hfp hnw) hJ

/-- **A checked `+`'s pending store is inside `W2`** at the frames `fs`
(`blkW_w2CP` at `blkW_placedS_upd`): a one-instruction block of the code
predicate at a node whose controls are placed in the slot file with the
store's slot `k0` updated to `%rax`'s word (`pendN2`'s `SlotRepAt`). -/
theorem blkW_w2Pend {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List (Directive × Nat)} {k0 : Int}
    (hcd : Spike.Lib.LowerX64.SubCd (CdC cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) (h1 : blk.length ≤ 1)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs (Spike.Lib.upd σ.slot k0 (σ.regs.get64 .rax)) c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  blkW_w2CP hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hcd hok hnr hab
    (blkW_placedS_upd hFS h1 hJp hrs hfp) hJ

/-- **A call's `callq g` is inside `W2`** at the frames `fs`
(`blkW_w2B`): at `BlC` (its placement and phase facts), at a node with the
body's offsets, in a region holding the return address's cell `8` below
the frame; `callq` writes its slot as its last (only) instruction. -/
theorem blkW_w2Call {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (h8 : (fr.size : Int) % 8 = 0)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND} (hno : n.o = oB fr)
    {ra : Int64} {zc : Nat} {g : Label} {k : Nat} (hbl : BlC cells okPc ph lab fr ra n.pc zc g k)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n [(i64 (.call (rel g)), zc)])
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n
      [(i64 (.call (rel g)), zc)] := by
  obtain ⟨L, j, off, hpc, hb, -, hph, -⟩ := hbl
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(i64 (.call (rel g)), zc)] := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc] at this
  have hok : okBlk (-(fr.size : Int) - 8) 16 n.o [(i64 (.call (rel g)), zc)] = true :=
    okBlk_callqC g zc (by rw [hno]; simp [offOk, oB]; omega)
  exact blkW_w2B hI hR hR8 hlo hhi hl hh hsub hfit hFO hFS hp hcode hph hok (noRet_callq g zc) rfl hab hJp hrs
    hfp hJ


/-- **The callee's entry is inside `W2`** at the frames `fs` (`CallPre`'s
`hWC` at `W2`): at the callee's label `fn`, `8` below the caller's frame
(the return address pushed), with the callee's prologue head there (`hb`)
and its phase facts (`hph`, `ProPh.hd`), in a region holding the head's
push of `%rbp` `16` below the frame: `SFacts` from the head's block
(`blkW_postO` at `okBlk_xHead_call`), nothing written, the node's controls
placed in the caller's slot file (`hJp`, the source not yet in the callee),
the abort phase's facts a premise (`hab`). -/
theorem nodeW_w2CalleeEntry {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (h8 : (fr.size : Int) % 8 = 0)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 16) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {fn : Label}
    (hb : Scc.Cert.Rt.X64.blockAtB cells fn 0 Spike.Lib.X64.Flow.xHead = true)
    (hph : blkPh okPc ph (fun _ => false) lab (lab fn + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    {n : ND} (hpc : n.pc = (_root_.Executable.labels exe).label fn)
    (hno : n.o = { oB fr with sp := (oB fr).sp - 8 })
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n := by
  have he : lab fn + Int64.ofNat 0 = n.pc := by rw [hpc, ← hI.labOk]; simp
  have hok : okBlk (-(fr.size : Int) - 16) 16 n.o Spike.Lib.X64.Flow.xHead = true := by
    rw [hno]; exact okBlk_xHead_call fr (Int.le_refl _) h8 (by omega)
  have hne : Spike.Lib.X64.Flow.xHead ≠ [] := by simp [Spike.Lib.X64.Flow.xHead]
  have HS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) Spike.Lib.X64.Flow.xHead :=
    Spike.Lib.X64.Rt.blkW_postO (n := dumN n) (dead := fun _ => false) (ra := 0) hI hb he hok hR hlo
    hhi hR8 hl hh (fun _ _ h => h.1 ▸ cfacts_c0) hph
    (fun _ _ _ k hk hr => (noRet_false Spike.Lib.X64.Rt.MainU.xHead_noRet k hk hr).elim) (fun _ _ _ => rfl)
    hsub hfit hFO
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc Spike.Lib.X64.Flow.xHead :=
    fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  have HW := BlkW.nodeW (blkW_noWr' (F := F) hcode hok hR (by omega) hhi) hne
  have HN := BlkW.nodeW (blkW_noSys' (R := R) (F := F) hcode hok) hne
  refine NodeW.w2 hp (BlkW.nodeW HS hne) (fun s c hA => ⟨⟨(hab s c hA).1, (nodeW_placedS hJp hrs hfp s c hA).1,
    fun _ _ _ _ => wrOkA_of_noWr (HW s c hA).1, fun h => absurd h (by rw [(HN s c hA).1]; decide)⟩,
    fun _ h => h⟩) hJ

end W

/-! ## The body's nodes' placements -/

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {i : Expr → String → Nat → Option Nat}
  {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr} {s : Spike.Lib.Form.SEnv}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **A body node's controls placed in the slot file** (`blkW_w2C`'s
`hJp`). -/
theorem slotRepAt_bodyN2 :
    ∀ σ c, (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).J σ c → SlotRepAt i lbl (rsOf fr) σ.slot c :=
  fun _ _ h => h.2.2.2

/-- **A pending store's controls placed in the updated slot file**
(`blkW_w2Pend`'s `hJp`). -/
theorem slotRepAt_pendN2 {k : Int} :
    ∀ σ c, (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k).J σ c →
      SlotRepAt i lbl (rsOf fr) (Spike.Lib.upd σ.slot k (σ.regs.get64 .rax)) c :=
  fun _ _ h => h.2.2.2

end Nodes

/--
info: 'Spike.Lib.LowerX64.blkW_w2C' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_w2C

/--
info: 'Spike.Lib.LowerX64.blkW_w2Call' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_w2Call

/--
info: 'Spike.Lib.LowerX64.blkW_w2Pend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_w2Pend

/--
info: 'Spike.Lib.LowerX64.nodeW_w2CalleeEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_w2CalleeEntry

end Spike.Lib.LowerX64
