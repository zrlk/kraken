/-
**A covered block of an `Accepted2` body inside `W2`** (AArch64; the twin
of `Spike/Lib/LowerX64/W2Body.lean`): the producer of `BlkW` at `W2`
(`Spike/Lib/LowerA64/SFactsA2.lean`) for a block of the code predicate
(`SubCd (CdC …)`), assembled from its parts (`BlkW.w2`,
`Spike/Lib/LowerA64/W2Blk.lean`):

- the state's facts: `SFacts` at the source start's control from the phase
  check (`blkW_postO` at `dumN`, `cfacts_c0`);
- the write obligation: a covered block writes nothing (`blkW_noWr`, the
  stack's cells are private), so `WrOkA` holds (`wrOkA_of_noWr`);
- the placement: `blkW_placedS` (`Spike/Lib/LowerA64/PlacedBlk.lean`) from
  the node's `SlotRepAt`, no slot written before the block's last
  instruction;
- the abort phase `AbSt`: a premise at the phase `Ab` the consumer picks;
- the node's controls: `main`'s `ret` excluded and `FrOk2`.

- `blkW_noSys`: a covered block's states off a system call (`W2Part`'s
  `print` output fact vacuous);
- `blkW_w2BP`, `blkW_w2CP`: as `blkW_w2B`, `blkW_w2C` with the placement a premise;
- `blkW_w2Pend`: at a checked `+`'s pending store (`blkW_placedS_upd`);
- `nodeW_w2CalleeEntry`: at a callee's entry (its prologue head);
- `slotRepAt_bodyN2`, `slotRepAt_pendN2`: the producers' `hJp` at the body's nodes;
- `blkW_w2B`: the producer at a block's placement and phase check;
- `blkW_w2C`: the producer at the code predicate;
- `blkW_w2Call`: the producer at a call's `bl` (`BlC`).
-/
import Spike.Lib.LowerA64.PlacedBlk
import Spike.Lib.LowerA64.Node2
import Spike.Lib.LowerA64.CallBlkW
import Spike.Lib.A64AllocG

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Scc.Cert.Rt.A64 (blockAt)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {rs : Scc.IR.Reg → Option Int}
  {B : Nat → Prop}

/-- **A covered block's states are off a system call** (`blkW_noWr`'s
cells: no covered instruction is an `svc`). -/
theorem blkW_noSys {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk := by
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  intro s σ c he hn _ _ _ _ _ k hk m _ _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, -, -⟩ := Spike.Lib.A64.Flow.okBlk_get (_root_.Executable.labels exe).label
    (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.A64.Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  refine Scc.Sem.A64.atSvc_false_of_cellAt hc fun imm h => ?_
  cases a <;> (try simp only [Spike.Lib.A64.Flow.AI.toDir] at h) <;> (try cases h)
  exact absurd (hreg _ _ rfl) (by simp [Spike.Lib.A64.Flow.RegOnly])

/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`, its states placed (`hP`): as `blkW_w2B` with the placement a
premise (a pending store's, `blkW_placedS_upd`). -/
theorem blkW_w2BP {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive} {L : Label} {j : Nat} (hb : blockAt prog L j blk = true)
    (he : lab L + Int64.ofNat (4 * j) = n.pc)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  rw [← he] at hph
  have hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk :=
    Spike.Lib.A64.Rt.blkW_postO (n := dumN n) (dead := fun _ => false) (ra := ra) hI hb he hok hR
      hal hlo hhi (fun _ _ h => h.1 ▸ cfacts_c0) hph (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim)
      (fun _ _ _ => rfl) hl hh hsub hfit hFO
  have hW : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.blkW_noWr hI hb he hok hR hal hlo hhi
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hW (blkW_noSys hI hb he hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2 hp hS ?_ hJ
  exact Spike.Lib.A64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`: a block `j` instructions after the label `L` (`hb`) at its
node's pc (`he`), passing the phase check there (`hph`), covered at its
node's offsets (`hok`), with no `ret` (`hnr`) and no slot written before its
last instruction (`hnw`), its states in the abort phase's facts (`hab`); at
a node whose controls are placed in the abstract slot file (`hJp`, every
slot a cell of the region), exclude `main`'s `ret` and are free of `ZBad`
(`hJ`), the suspended frames placed under the frame condition (`hfp`). -/
theorem blkW_w2B {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive} {L : Label} {j : Nat} (hb : blockAt prog L j blk = true)
    (he : lab L + Int64.ofNat (4 * j) = n.pc)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) (hnw : noSlotWr blk.dropLast = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  exact blkW_w2BP hI hR hal hlo hhi hl hh hsub hfit hFO hp hb he hph hok hnr hab
    (blkW_placedS hFS hJp hrs hfp hnw) hJ

/-- **A covered block of the code without a `ret` is inside `W2`** at the
frames `fs`, its states placed (`hP`): as `blkW_w2C` with the placement a
premise (`blkW_w2BP`). -/
theorem blkW_w2CP {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive}
    (hcd : SubCd (CdC prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  have he : lab L + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
  rw [hpc] at hph
  exact blkW_w2BP hI hR hal hlo hhi hl hh hsub hfit hFO hp (blockAt_sub hb) he hph hok hnr hab hP hJ

/-- **A covered block of the code without a `ret` is inside `W2`** at the
frames `fs` (`blkW_w2B`): a block of the code predicate `CdC` at a return
address `ra` (`SubCd`, its phase from the run's check). -/
theorem blkW_w2C {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive}
    (hcd : SubCd (CdC prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) (hnw : noSlotWr blk.dropLast = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk := by
  exact blkW_w2CP hI hR hal hlo hhi hl hh hsub hfit hFO hp hcd hok hnr hab
    (blkW_placedS hFS hJp hrs hfp hnw) hJ

/-- **A checked `+`'s pending store is inside `W2`** at the frames `fs`
(`blkW_w2CP` at `blkW_placedS_upd`): a one-instruction block of the code
predicate at a node whose controls are placed in the slot file with the
store's slot `k0` updated to `x9`'s word (`pendN2`'s `SlotRepAt`). -/
theorem blkW_w2Pend {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive} {k0 : Int}
    (hcd : SubCd (CdC prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) (h1 : blk.length ≤ 1)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs (Spike.Lib.upd σ.slot k0 σ.regs.X9.toBitVec) c)
    (hrs : ∀ r k, rs r = some k → R.Off k) (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  blkW_w2CP hI hR hal hlo hhi hl hh hsub hfit hFO hp hcd hok hnr hab
    (blkW_placedS_upd hFS h1 hJp hrs hfp) hJ

/-- **A call's `bl g` is inside `W2`** at the frames `fs` (`blkW_w2B`): at
`BlC` (its placement and phase facts), in any region holding the frame
(`bl` writes `x30` only, no slot). -/
theorem blkW_w2Call {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : Scc.Emit.A64.FnCtx}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {n : ND}
    {ra : Int64} {g : Label} {k : Nat} (hbl : BlC prog okPc ph lab cx ra n.pc g k)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n [blD g])
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n [blD g] := by
  obtain ⟨L, j, hpc, hb, -, hph, -⟩ := hbl
  exact blkW_w2B (lo := -(cx.frame : Int)) (hi := 0) hI hR hal hlo hhi hl hh hsub hfit hFO hFS hp hb hpc hph
    (Spike.Lib.A64.Flow.okBlk_blD _ _ _ g) (noRet_bl g) rfl hab hJp hrs hfp hJ


/-- **The callee's entry is inside `W2`** at the frames `fs` (`call_ndSF`'s
`hWC` at `W2`): at the callee's label `fn`, at the caller's frame offsets
(`bl` pushes nothing), with the callee's stack check label `sc` right after
it (`hgap`), its head there (`hb`) and its phase facts (`hph`,
`ProPh.hd`), in any region holding the caller's frame: `SFacts` from the
head's block (`blkW_postO` at `okBlk_chkHead_at`), nothing written, the
node's controls placed in the caller's slot file (`hJp`, the source not yet
in the callee), the abort phase's facts a premise (`hab`). -/
theorem nodeW_w2CalleeEntry {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {cx : Scc.Emit.A64.FnCtx}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {fn sc : Label} {Z : Int64}
    (hgap : Scc.Cert.Rt.A64.labelGap prog fn sc 0 = true)
    (hb : blockAt prog sc 0 (Spike.Lib.A64.Flow.chkHead Z) = true)
    (hph : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 0)) 0 (Spike.Lib.A64.Flow.chkHead Z) = true)
    {n : ND} (hpc : n.pc = (_root_.Executable.labels exe).label fn) (hno : n.o = Spike.Lib.LowerA64.oF cx)
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n)
    (hJp : ∀ σ c, n.J σ c → SlotRepAt Λ.imms lbl rs σ.slot c) (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n := by
  have he : lab sc + Int64.ofNat (4 * 0) = n.pc := by
    rw [hpc, ← hI.labOk, Scc.Cert.Rt.A64.label_labelGap hI.lays hgap, Spike.Lib.A64.Flow.ofNat4_zero,
      Spike.Lib.A64.Flow.ofNat4_zero]
  have hok : okBlk (-(cx.frame : Int)) 0 n.o (Spike.Lib.A64.Flow.chkHead Z) = true := by
    rw [hno]; exact okBlk_chkHead_at _ _ _ Z
  have hne : Spike.Lib.A64.Flow.chkHead Z ≠ [] := by simp [Spike.Lib.A64.Flow.chkHead]
  have HS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) (Spike.Lib.A64.Flow.chkHead Z) :=
    Spike.Lib.A64.Rt.blkW_postO (n := dumN n) (dead := fun _ => false) (ra := 0) hI hb he hok hR hal
    hlo hhi (fun _ _ h => h.1 ▸ cfacts_c0) hph
    (fun _ _ _ k hk r hr => (noRet_false (Spike.Lib.A64.Rt.MainU.chkHead_noRet Z) k hk r hr).elim)
    (fun _ _ _ => rfl) hl hh hsub hfit hFO
  have HW := BlkW.nodeW (Spike.Lib.A64.AllocG.blkW_noWr (F := F) hI hb he hok hR hal hlo hhi) hne
  have HN := BlkW.nodeW (blkW_noSys (R := R) (F := F) hI hb he hok) hne
  refine NodeW.w2 hp (BlkW.nodeW HS hne) (fun s c hA => ⟨⟨(hab s c hA).1, (nodeW_placedS hJp hrs hfp s c hA).1,
    fun _ _ _ _ => wrOkA_of_noWr (HW s c hA).1, fun h => absurd h (by rw [(HN s c hA).1]; decide)⟩,
    fun _ h => h⟩) hJ

end W

/-! ## The body's nodes' placements -/

section Nodes

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {i : Expr → String → Nat → Option Nat}
  {cx : Scc.Emit.A64.FnCtx} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr} {s : Spike.Lib.Form.SEnv}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **A body node's controls placed in the slot file** (`blkW_w2C`'s
`hJp`). -/
theorem slotRepAt_bodyN2 :
    ∀ σ c, (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).J σ c → SlotRepAt i lbl (rsOf cx) σ.slot c :=
  fun _ _ h => h.2.2.2

/-- **A pending store's controls placed in the updated slot file**
(`blkW_w2Pend`'s `hJp`). -/
theorem slotRepAt_pendN2 {k : Int} :
    ∀ σ c, (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k).J σ c →
      SlotRepAt i lbl (rsOf cx) (Spike.Lib.upd σ.slot k σ.regs.X9.toBitVec) c :=
  fun _ _ h => h.2.2.2

end Nodes

/--
info: 'Spike.Lib.LowerA64.blkW_w2C' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_w2C

/--
info: 'Spike.Lib.LowerA64.blkW_w2Call' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_w2Call

/--
info: 'Spike.Lib.LowerA64.blkW_w2Pend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_w2Pend

/--
info: 'Spike.Lib.LowerA64.nodeW_w2CalleeEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_w2CalleeEntry

end Spike.Lib.LowerA64
