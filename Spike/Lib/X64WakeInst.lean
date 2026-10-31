/-
**wake.w on x86-64: the concrete instance data after the spawn** (hello
plan 1.6; x86-64 twin of `Spike/Lib/WakeInst.lean`). The ghost record, both
threads' memory sides, the location data, main's side `MSide`, and `wakeQ`
at them, for a placed output (`L := RuntimeLayout.ofPlaceWX hp i`, its
canonical memory `m0`), with main owning its self word `⟨T, 8⟩` and the
worker its `⟨W, 8⟩` (`X64WakeOwnX.wakeOwnXW T W`).

- `Gh`: the ghost record `ι` (as on AArch64).
- `wakeSR g`: the spawn record `⟨T, S, lbl, lsize⟩`.
- `wakeG' g`: the value invariant (`X64WakeGOf2.GOf2`, any value at `cT`).
- `wakeMs g`: **both threads' base memory side**: the consumer's `msOf` at
  read side the numbers, value invariant `wakeG'`, no owned word, the spawn's
  placement, its runtime writes narrowed to words outside every placed label.
- `msM g`, `msW g`: main's and the worker's memory sides, `wakeMs g` owning
  the thread's self word with its runtime writes off both self words
  (`X64WakeOwnX.msXW`).
- `rd_num`: a word `wakeMs` reads representing `1` is the number `1`.
- `rtOff_msXW`: the runtime words of either side are outside every placed
  label (`X64WakeInst.RtOff`, `main_closed_wakeWR`'s `hms`).
- `SelfOK T W g`, `wakeLocs g`, `wakeLocs_ok`: the self words' separation
  premise; the location data (`X64WakeOwnX.wakeLocsXW` at `msM`/`msW`'s base);
  its separation facts.
- `mainInv`, `mainInv_closed`, `mainInv_W`, `mainInv_of`: the union of the
  invariants closed under main's rows inside a fragment.
- `wakeM lab μT hoff`: **main's `MSide`** (`Mi := mainInv … (mainWR …)`).
- `wakeQI`: `X64WakeQ.wakeQ` at these.
- Fields: `lbl0_I`, `K0_I`, `G0_I`, `own0_I`, `ownConst0_I`, `ownMp0_I`,
  `ownCov0_I`, `hMμ_I`, `live0_I`, `wideX_I`, `wide0_I`, `placed_I`,
  `relW0_I`, `hhalt0_I`, `labMapped_I`, `hmapM_I`, `noSite0_I`, `noWrite0_I`,
  `mpW0_I`, `mpW_I`, `cTfoot_I`, `cSfrz_I`, `footLab_I`.

**Where this differs from AArch64**: the owned words are the two self words
(`wakeOwnXW T W`, A64: none), so main's memory side is `msM g := msXW
(wakeMs g) T T W` (A64: `wakeMs g` itself), the worker's `msW g := msXW
(wakeMs g) W T W`, and `WCompat0.own0` reads `wakeOwnXW` with the new fields
`ownConst0_I`, `ownMp0_I`, `ownCov0_I`; `wakeLocs` is `wakeLocsXW` (each
thread owns its self word), so `wakeLocs_ok` and `footLab_I` carry
`SelfOK T W` (the two words distinct, outside every placed label, `cT` not
main's; discharged at the instance from the TCBs' placement in the runtime
region, as `X64WakeOwnXW.wakeLocsXW_ok`'s premises). `wakeQI` takes the
store point `passT` and `T W` (`X64WakeQ.wakeQ`'s parameters). The system
call numbers are `futex` `202`, `exit_group` `231` (`X64WakeMainS.MainSys`).
`hrt8_of_limOk` is `X64WakeInst.htp8_of_limOk` (`X64WakeInstR`) with
`rtOff_msXW`; `mainW`, `mainWR` are `X64WakeMainWDef`'s and
`X64WakeInstR`'s. `flagLd_I` is not here (follow-up).
-/
import Spike.Lib.X64WakeInstR
import Spike.Lib.X64WakeQ
import Spike.Lib.X64AbOffL
import Spike.Lib.X64WakeGOf2
import Spike.Lib.WakeG

namespace Spike.Lib.X64WakeInst

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeP
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (m0Of)
open Spike.Lib.X64Consumer (msOf K0)
open Spike.Lib.X64WakeOwnX (msXW wakeOwnXW wakeLocsXW)
open Spike.Lib.WakeMLive (wlRet)

/-- **The ghost record** of the two-thread phase. -/
structure Gh where
  /-- The target memory's last message at the spawn. -/
  T : Nat
  /-- The source memory's size at the spawn. -/
  S : Nat
  /-- The placement at the spawn. -/
  lbl : WeakMem.AllocLabel → Option Nat
  lsize : WeakMem.AllocLabel → Nat
  /-- The flag's source address and target word. -/
  cS : WeakMem.Address
  cT : Loc
  /-- main's and the worker's pointer words for `c`. -/
  cwM : TermRun.Word
  cwW : TermRun.Word
  /-- main's park permit word. -/
  pT : Loc

/-- **The spawn record.** -/
def wakeSR (g : Gh) : SpawnRec := ⟨g.T, g.S, g.lbl, g.lsize⟩

/-- **The self words' separation**: main's `⟨T, 8⟩` and the worker's
`⟨W, 8⟩` differ, lie outside every placed label, and the flag's word is not
main's (`X64WakeOwnX.wakeLocsXW_ok`'s premises). -/
def SelfOK (T W : BitVec 64) (g : Gh) : Prop :=
  (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩ ∧ ¬ InLabel g.lbl g.lsize ⟨T, 8⟩ ∧ ¬ InLabel g.lbl g.lsize ⟨W, 8⟩ ∧
    g.cT ≠ ⟨T, 8⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)

/-- **The value invariant**: the consumer's with the second TCB's limit word
also pinned (`X64WakeGOf2.GOf2`), with any value at the flag's word. -/
def wakeG' (g : Gh) : Loc → Val → Prop :=
  WakeG.wakeG (X64WakeGOf2.GOf2 (RuntimeLayout.ofPlaceWX hp i)
    (m0Of (RuntimeLayout.ofPlaceWX hp i).Λ o.prog o.secs)) g.cT

/-- **Both threads' base memory side**: `msOf` (read side the numbers, value
invariant `wakeG'`, no owned word, the spawn's placement) with its runtime
writes narrowed to words outside every placed label. -/
def wakeMs (g : Gh) : MemSide isa :=
  { msOf (RuntimeLayout.ofPlaceWX hp i).Λ (Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i))
      (fun w => ∃ n, w.val = .num n)
      (wakeG' hp i g) (fun _ => []) g.lbl g.lsize with
    mp := fun L w => Scc.Sem.Kernel.mapped (K0 (RuntimeLayout.ofPlaceWX hp i).Λ) w L = true ∧
      (w = true → Consumer1.LocIn (RuntimeLayout.ofPlaceWX hp i).Λ.shared L ∧ ¬ InLabel g.lbl g.lsize L) }

/-- **main's memory side**: `wakeMs` owning `⟨T, 8⟩`, its runtime writes off
both self words. -/
def msM (g : Gh) : MemSide isa := msXW (wakeMs hp i g) T T W

/-- **The worker's memory side**: `wakeMs` owning `⟨W, 8⟩`, its runtime
writes off both self words (`X64WakeAssembly`'s `hms` at `msW := wakeMs`). -/
def msW (g : Gh) : MemSide isa := msXW (wakeMs hp i g) W T W

/-- **A word `wakeMs` reads representing `1` is the number `1`.** -/
theorem rd_num (g : Gh) (O : BitVec 64) (w' : TermRun.Word) (hr : (msXW (wakeMs hp i g) O T W).rd w')
    (hv : ValRep g.lbl w'.val 1) : w'.val = .num 1 := by
  obtain ⟨n, hn⟩ := hr
  rw [hn] at hv ⊢
  rw [hv.2]

/-- **Either side's runtime words are outside every placed label**
(`main_closed_wakeWR`'s `hms`; the x86-64 `WakeInst.hrt8_of_limOk` is
`htp8_of_limOk` with it). -/
theorem rtOff_msXW (g : Gh) (O : BitVec 64) : RtOff g.lbl g.lsize (msXW (wakeMs hp i g) O T W) :=
  fun _ h => h

/-- **The location data**: each thread owns its self word; its other
footprint words the runtime words its side lets it write. -/
def wakeLocs (g : Gh) : WakeLocs :=
  wakeLocsXW g.lbl g.lsize g.cT g.cS (wakeMs hp i g) (wakeMs hp i g) T W

/-- `wakeLocs`' separation facts, given the self words' (`SelfOK`). -/
theorem wakeLocs_ok (g : Gh) (h : SelfOK T W g) : (wakeLocs hp i T W g).OK :=
  X64WakeOwnX.wakeLocsXW_ok h.1 h.2.1 h.2.2.1 h.2.2.2 (fun _ h => (h.2 rfl).2) (fun _ h => (h.2 rfl).2)

end Inst

/-! ## main's side -/

/-- **The union of the invariants closed under main's rows inside `W`.** -/
def mainInv (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isa) (W : Frag isa) : Frag isa :=
  fun s c => ∃ inv : Frag isa, (∀ s c, inv s c → OutL X64WakeT1.wakeSrc lbl ms inv s c) ∧
    (∀ s c, inv s c → W s c) ∧ inv s c

theorem mainInv_closed {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {W : Frag isa} :
    ∀ s c, mainInv lbl ms W s c → OutL X64WakeT1.wakeSrc lbl ms (mainInv lbl ms W) s c := by
  rintro s c ⟨inv, hcl, hW, hi⟩
  exact (hcl s c hi).mono fun s c h => ⟨inv, hcl, hW, h⟩

theorem mainInv_W {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {W : Frag isa} :
    ∀ s c, mainInv lbl ms W s c → W s c :=
  fun s c ⟨_, _, hW, hi⟩ => hW s c hi

/-- A state of an invariant closed under the rows inside `W` is in
`mainInv` (`main_closed_wakeWR`'s output). -/
theorem mainInv_of {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {W : Frag isa}
    {inv : Frag isa} (hW : ∀ s c, inv s c → W s c)
    (hcl : ∀ s c, inv s c → OutL X64WakeT1.wakeSrc lbl ms inv s c)
    {s : isa.State} {c : Ctl} (h : inv s c) : mainInv lbl ms W s c :=
  ⟨inv, hcl, hW, h⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)

/-- **main's side** at labels `lab` and marks `μT`, given that `AbOffA lab`
is off every abort site of `μT` (`hoff`), over the ghost records satisfying
`ok`. -/
def wakeM (ok : Gh → Prop) (lab : String → Int64) (μT : Marks)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a) :
    X64WakeM0.MSide {g : Gh // ok g} where
  lbl g := g.1.lbl
  ms g := msM hp i T W g.1
  Mi g := mainInv g.1.lbl (msM hp i T W g.1)
    (mainWR lab (RuntimeLayout.ofPlaceWX hp i).exe (RuntimeLayout.ofPlaceWX hp i).Λ g.1.lbl g.1.lsize)
  closed _ := mainInv_closed
  cw g := g.1.cwM
  μ := μT
  off _ s c h := hoff s c (mainInv_W s c h).1.1

/-- **wake's relation** at the instance (`R1`, the worker's side `D`, the
marks `μT`, `KR`'s ranges and the store point `passT` given), over the ghost
records satisfying `ok`. -/
def wakeQI (ok : Gh → Prop) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μT : Marks)
    (M : X64WakeM0.MSide {g : Gh // ok g}) (D : X64WakeW1.WSide {g : Gh // ok g})
    (r0 r1 : {g : Gh // ok g} → Range) (passT : State → Prop) : WakeRel :=
  X64WakeQ.wakeQ arch R1 {g : Gh // ok g} (wakeSR ·.1) (·.1.cT) (·.1.cS) (·.1.pT)
    (fun g => wakeP abi μT (wakeLocs hp i T W g.1)) (fun g => wakeG' hp i g.1) M D r0 r1 passT T W

/-! ## The definitional fields -/

variable {ok : Gh → Prop} {lab : String → Int64} {μT : Marks}
  {hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {D : X64WakeW1.WSide {g : Gh // ok g}}
  {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop}

local notation "MI" => wakeM hp i T W ok lab μT hoff
local notation "QI" => wakeQI hp i T W ok arch R1 μT (wakeM hp i T W ok lab μT hoff) D r0 r1 passT

/-- `WCompat0.lbl0`. -/
theorem lbl0_I : ∀ w, (MI).lbl w = ((QI).SR w).lbl := fun _ => rfl

/-- `WCompat0.K0`. -/
theorem K0_I : ∀ w, ((MI).ms w).K = some abi := fun _ => rfl

/-- `WCompat0.G0` (and `WCompat.G` for `D.ms := msW hp i T W`). -/
theorem G0_I : ∀ w, ((MI).ms w).G = (QI).G w := fun _ => rfl

/-- `WCompat0.own0`: main owns `wakeOwnXW`'s words of thread 0. -/
theorem own0_I : ∀ w s, ((MI).ms w).own s = (QI).own w 0 s [] := fun _ _ => rfl

/-- `WCompat0.ownConst0`. -/
theorem ownConst0_I : ∀ w s s', (QI).own w 0 s' [] = (QI).own w 0 s [] := fun _ _ _ => rfl

/-- `WCompat0.ownMp0`. -/
theorem ownMp0_I : ∀ w s L v, (L, v) ∈ (QI).own w 0 s [] → ¬ ((MI).ms w).mp L true :=
  fun w s L v hm => X64WakeOwnX.ownMp0XW (wakeMs hp i w.1) T W w s L v hm

/-- `WCompat0.ownCov0`. -/
theorem ownCov0_I : ∀ w s L v, (L, v) ∈ (QI).own w 0 s [] → ((QI).P w).cov 0 L :=
  fun w s L v hm => X64WakeOwnX.ownCov0XW T W w s L v hm

/-- `WakeAssembly`'s `hMμ`: main's side's marks are `μT`. -/
theorem hMμ_I : (MI).μ = μT := rfl

/-- `WCompat0.live0`. -/
theorem live0_I : ∀ w s c, (MI).Mi w s c → c.term ≠ wlRet :=
  fun _ s c h => (mainInv_W s c h).1.2.1

/-- main's states are wide on the layout's executable (`WCompat0.wide0`,
`sysExec0`). -/
theorem wideX_I : ∀ w s c, (MI).Mi w s c →
    Spike.Lib.X64.WideKeep.WideX (RuntimeLayout.ofPlaceWX hp i).exe s :=
  fun _ s c h => (mainInv_W s c h).1.2.2.1

/-- `WCompat0.wide0`. -/
theorem wide0_I : ∀ w s c, (MI).Mi w s c → Scc.Cert.WideX64.WideSt s :=
  fun w s c h => (wideX_I hp i T W w s c h).1

/-- main's environment is placed at the spawn's placement. -/
theorem placed_I : ∀ w s c, (MI).Mi w s c →
    Spike.Lib.X64Consumer.Placed (RuntimeLayout.ofPlaceWX hp i).Λ (wakeSR w.1).lbl s c :=
  fun _ s c h => (mainInv_W s c h).1.2.2.2

/-- `WCompat0.relW0`: main's instructions write at most once, a release
write. -/
theorem relW0_I : ∀ w s c e, (MI).Mi w s c → isa.exec s = some e → EvTree.RelW1 Arch.tso e :=
  fun _ s c _ h he => (mainInv_W s c h).2.1.2 _ he

/-- `WakeAssembly`'s `hhalt0`: main's states run (at a system call too). -/
theorem hhalt0_I : ∀ w s c, (MI).Mi w s c → abi.atSys s = true → (isa.exec s).isSome :=
  fun _ s c h _ => (mainInv_W s c h).2.1.1

/-- `X64WakeMappedRow.hM_of`'s `hlab`: main's label words are mapped in `K0`. -/
theorem labMapped_I : ∀ w s c, (MI).Mi w s c →
    Spike.Lib.X64WakeMappedRow.LabMapped ((MI).lbl w) (K0 (RuntimeLayout.ofPlaceWX hp i).Λ) c :=
  fun _ s c h => (mainInv_W s c h).2.2.1

/-- `WakeAssembly`'s `hmapM` (`X64WakeMappedRow.hM_of`): main's instructions
touch only locations mapped in `K0`. -/
theorem hmapM_I : ∀ w s c, (MI).Mi w s c → abi.atSys s = false →
    ∀ e, isa.exec s = some e →
      ¬ Scc.Sem.Kernel.Touches
        (fun l w => Scc.Sem.Kernel.mapped (K0 (RuntimeLayout.ofPlaceWX hp i).Λ) w l = false) e :=
  Spike.Lib.X64WakeMappedRow.hM_of (fun _ => rfl) (fun _ _ _ h => h.1.1) (labMapped_I hp i T W)

/-- `WCompat0.noSite0` at the placed output's marks (`X64AbOffL.noSite_of_A_ofPlaceOK`),
for `lab` the layout's labels. -/
theorem noSite0_I (hlab : lab = (RuntimeLayout.ofPlaceWX hp i).lab) : ∀ w s c, (MI).Mi w s c →
    Scc.Sem.Kernel.siteAt abi (Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i)) s = none := by
  subst hlab
  exact fun _ s c h => Spike.Lib.X64AbOffL.noSite_of_A_ofPlaceOK hp i (mainInv_W s c h).1.1

/-- `WCompat0.noWrite0`: main's system calls are `futex` or `exit_group`
(`MainSys`), never `write`. -/
theorem noWrite0_I : ∀ w s c fd buf n, (MI).Mi w s c → abi.atSys s = true →
    Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n) := by
  intro _ s c fd buf n h ha
  show Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 s.st.1.regs.rax.toNat _ ≠ _
  rcases (mainInv_W s c h).2.2.2.1 ha with h | h <;> rw [h] <;>
    simp [Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64] <;> repeat (first | split | simp)

/-- `WCompat0.mpW0`. -/
theorem mpW0_I : ∀ w L, ((MI).ms w).mp L true →
    ((QI).P w).foot 0 L ∧ ¬ InLabel ((QI).SR w).lbl ((QI).SR w).lsize L ∧
      Consumer1.LocIn (RuntimeLayout.ofPlaceWX hp i).Λ.shared L :=
  fun _ _ h => ⟨.inr (.inl h), (h.1.2 rfl).2, (h.1.2 rfl).1⟩

/-- `WCompat.mpW` for the worker's memory side `msW hp i T W`. -/
theorem mpW_I : ∀ w : {g : Gh // ok g}, ∀ L, (msW hp i T W w.1).mp L true →
    ((QI).P w).foot 1 L ∧ ¬ InLabel ((QI).SR w).lbl ((QI).SR w).lsize L ∧
      Consumer1.LocIn (RuntimeLayout.ofPlaceWX hp i).Λ.shared L :=
  fun _ _ h => ⟨.inr (.inl h), (h.1.2 rfl).2, (h.1.2 rfl).1⟩

/-- `WCompat.cTfoot`. -/
theorem cTfoot_I : ∀ w, ((QI).P w).foot 1 ((QI).C w).cT := fun _ => wakeP_foot_c

/-- `WCompat.cSfrz`. -/
theorem cSfrz_I : ∀ w, ¬ ((QI).P w).frzS ((QI).C w).cS := fun _ => wakeP_not_frzS_c

/-- `WCompat.footLab`, given the self words' separation (`SelfOK`). -/
theorem footLab_I (hself : ∀ w : {g : Gh // ok g}, SelfOK T W w.1) : ∀ w L, ((QI).P w).foot 1 L →
    InLabel ((QI).SR w).lbl ((QI).SR w).lsize L → L = ((QI).C w).cT :=
  fun w _ hf hl => wakeP_footLab (wakeLocs_ok hp i T W w.1 (hself w)) hf hl

end Inst

end Spike.Lib.X64WakeInst

/-- info: 'Spike.Lib.X64WakeInst.rd_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.rd_num

/-- info: 'Spike.Lib.X64WakeInst.wakeLocs_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.wakeLocs_ok

/-- info: 'Spike.Lib.X64WakeInst.hmapM_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.hmapM_I

/-- info: 'Spike.Lib.X64WakeInst.noSite0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.noSite0_I

/-- info: 'Spike.Lib.X64WakeInst.noWrite0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.noWrite0_I

/-- info: 'Spike.Lib.X64WakeInst.mpW0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.mpW0_I

/-- info: 'Spike.Lib.X64WakeInst.footLab_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.footLab_I

/-- `SelfOK` is inhabited (a non-vacuity check): two
distinct self words, no placed label, the flag's word a third. -/
example : Spike.Lib.X64WakeInst.SelfOK 0x1000#64 0x2000#64
    { T := 0, S := 0, lbl := fun _ => none, lsize := fun _ => 0, cS := ⟨0, 0⟩, cT := ⟨0x3000#64, 8⟩,
      cwM := TermRun.cst (.num 0), cwW := TermRun.cst (.num 0), pT := ⟨0x4000#64, 8⟩ } :=
  ⟨by decide, fun ⟨_, _, h, _⟩ => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h), by decide⟩
