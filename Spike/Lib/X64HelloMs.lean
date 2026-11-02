/-
**hello.w on x86-64: both threads' memory side and location data at a placed output** (the twin of
`Spike/Lib/HelloMs.lean`; as `X64WakeInst.wakeMs` / `wakeLocs` and their `WCompat0` field lemmas, at hello's
records: any runtime layout `L`, value invariant `G`, placement `lbl`/`lsize`).

- `helloMs L G lbl lsize`: the consumer's `msOf` at read side the numbers (`∃ n, w.val = .num n`), value
  invariant `G`, no owned word, the placement, with its runtime writes narrowed to words outside every placed
  label (as `wakeMs`, at `L`'s layout and marks `PhRec.μ L`).
- `tcbWH L`: hello's second TCB's self word `pinA + 112`; `tcbM_ne_tcbWH`.
- `helloLocs L lbl lsize cT cS`: `X64WakeOwnX.wakeLocsXW` at `tcbM L`, `tcbWH L` (main owns `⟨tcbM L, 8⟩`, the
  worker `⟨tcbWH L, 8⟩`; each thread's other footprint the words `helloMs` lets it write, off both self words);
  `helloLocs_ok` (given both self words off every placed label and `cT` not main's word), `helloLocs_okG` (at a
  record's `X64WakeInst.SelfOK`).
- `msH L G SR w`: the memory side at record `w`; `msHX L G SR w`: main's, `msH` owning `tcbM L`
  (`X64WakeOwnX.msXW`).
- The memory side's facts `X64HelloCompat0.hC0H` / `X64HelloCompatI.hC0P` read: `K_H`, `G_H`, `rt_H`, `rdN_H`,
  `abt_H`, `noProm_H`; at `msHX`: `own_H`, `ownConst_H`, `ownMp_H`, `ownCov_H` and `mpW_H` (the footprint at
  `Pa := X64HelloInst.helloP abi μ (helloLocs …)`); the worker's `ownCov1_H`.
- `hC0Ms`: `X64HelloCompatI.hC0P` at `ms := msHX L G SR`, `Pa := helloP abi μP (helloLocs …)`; open: main's
  pointer word `hcw`.

**Where this differs from AArch64** (forced by the x86-64 shape): the memory side is over `X64.isa` and the
consumer's `X64Consumer.msOf`/`K0` (AArch64: `isaLSE2`, `A64Consumer`), the placed output a `PlaceWX` with layout
`RuntimeLayout.ofPlaceWX` and its text an `Scc.Sem.X64.Asm` whose cells are the output's (`cellsOf`; AArch64:
`textProgram`); certification is at `Arch.tso` (AArch64: `Arch.armv8`). As wake's x86-64 instance, and unlike
AArch64 (no owned word), main's side owns its TCB's self word (`scc_rt_park` reads `%fs:0` as an owned value), the
worker's its own, so the location data owns both and its separation facts need `SelfOK` (`tcbWH`, `msHX`,
`helloLocs_ok`'s premises, `ownConst_H`/`ownMp_H`/`ownCov_H`/`ownCov1_H` are x86-64 only). `helloP` is
`X64HelloInstFrz`'s.
-/
import Spike.Lib.X64HelloCompatI
import Spike.Lib.X64HelloInstFrz

namespace Spike.Lib.X64HelloMs

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeP
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (msOf K0)
open Spike.Lib.X64HelloMainInv (helloM)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64HelloInst (helloP)
open Spike.Lib.X64.WakePh (tcbM)
open Spike.Lib.X64WakeOwnX (msXW wakeOwnXW wakeLocsXW wakeLocsXW_ok ownMpXW ownCov0XW ownCov1XW)

/-- **Both threads' memory side** (see the module doc). -/
def helloMs (L : RuntimeLayout) (G : Loc → Val → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) : MemSide isa :=
  { msOf L.Λ (Spike.Lib.X64.PhRec.μ L) (fun w => ∃ n, w.val = .num n) G (fun _ => []) lbl lsize with
    mp := fun Lc w => Scc.Sem.Kernel.mapped (K0 L.Λ) w Lc = true ∧
      (w = true → Consumer1.LocIn L.Λ.shared Lc ∧ ¬ InLabel lbl lsize Lc) }

/-- **hello's second TCB's self word** `pinA + 112` (the second `scc_rt_alloc_tcb`'s TCB, its header at
`pinA + 104`; `X64HelloWcSp3.tH` at the layout's labels). -/
abbrev tcbWH (L : RuntimeLayout) : BitVec 64 := L.pinA + 112#64

/-- The two TCB words differ. -/
theorem tcbM_ne_tcbWH (L : RuntimeLayout) : tcbM L ≠ tcbWH L := by
  show L.pinA + 8#64 ≠ L.pinA + 112#64
  bv_omega

/-- **The location data** (`X64WakeOwnX.wakeLocsXW` at `T := tcbM L`, `W := tcbWH L`): main owns `⟨tcbM L, 8⟩`,
the worker `⟨tcbWH L, 8⟩`; each thread's other footprint words the runtime words `helloMs` lets it write, off both
self words. -/
abbrev helloLocs (L : RuntimeLayout) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (cT : Loc) (cS : WeakMem.Address) : WakeLocs :=
  wakeLocsXW lbl lsize cT cS (helloMs L (fun _ _ => True) lbl lsize) (helloMs L (fun _ _ => True) lbl lsize)
    (tcbM L) (tcbWH L)

/-- **`helloLocs`' separation facts**, given both self words outside every placed label and the flag's word not
main's (`X64WakeInst.SelfOK`'s last three parts; the two self words differ by `tcbM_ne_tcbWH`). -/
theorem helloLocs_ok (L : RuntimeLayout) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (cT : Loc) (cS : WeakMem.Address)
    (hTl : ¬ InLabel lbl lsize ⟨tcbM L, 8⟩) (hWl : ¬ InLabel lbl lsize ⟨tcbWH L, 8⟩) (hcT : cT ≠ ⟨tcbM L, 8⟩) :
    (helloLocs L lbl lsize cT cS).OK :=
  wakeLocsXW_ok (fun h => tcbM_ne_tcbWH L (congrArg Loc.addr h)) hTl hWl hcT (fun _ h => (h.2 rfl).2)
    (fun _ h => (h.2 rfl).2)

/-- **`helloLocs_ok` at a ghost record** satisfying `X64WakeInst.SelfOK (tcbM L) (tcbWH L)`. -/
theorem helloLocs_okG (L : RuntimeLayout) (g : X64WakeInst.Gh)
    (hself : X64WakeInst.SelfOK (tcbM L) (tcbWH L) g) : (helloLocs L g.lbl g.lsize g.cT g.cS).OK :=
  helloLocs_ok L _ _ _ _ hself.2.1 hself.2.2.1 hself.2.2.2

section Fields

variable {ι : Type} (L : RuntimeLayout) (G : ι → Loc → Val → Prop) (SR : ι → SpawnRec)

/-- The memory side at record `w`. -/
abbrev msH (w : ι) : MemSide isa := helloMs L (G w) (SR w).lbl (SR w).lsize

/-- **main's memory side at record `w`**: `msH` owning `tcbM`, its runtime writes off both self words
(`X64WakeOwnX.msXW`). -/
abbrev msHX (w : ι) : MemSide isa := msXW (msH L G SR w) (tcbM L) (tcbM L) (tcbWH L)

/-- `WCompat0.K0`. -/
theorem K_H : ∀ w, (msH L G SR w).K = some abi := fun _ => rfl

/-- `WCompat0.G0`. -/
theorem G_H : ∀ w, (msH L G SR w).G = G w := fun _ => rfl

/-- main's side owns `tcbM` holding `tcbM` (`X64WakeOwnX.wakeOwnXW`'s thread `0`). -/
theorem own_H : ∀ w s, (msHX L G SR w).own s = [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] := fun _ _ => rfl

/-- `WCompat0.ownConst0`: main's owned words do not depend on its state. -/
theorem ownConst_H : ∀ w s s', (msHX L G SR w).own s' = (msHX L G SR w).own s := fun _ _ _ => rfl

/-- `WCompat0.ownMp0`: main never writes its owned word as the runtime's. -/
theorem ownMp_H : ∀ w s Lc v, (Lc, v) ∈ (msHX L G SR w).own s → ¬ (msHX L G SR w).mp Lc true :=
  fun _ s Lc v h => ownMpXW (.inl rfl) s Lc v h

/-- `WCompat0.ownCov0` at `Pa := helloP abi μ (helloLocs …)`: main's owned word is in its cover set. -/
theorem ownCov_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w s Lc v, (Lc, v) ∈ (msHX L G SR w).own s →
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).cov 0 Lc :=
  fun w s Lc v h => ownCov0XW _ _ w s Lc v h

/-- The worker's `ownCov1` at `Pa := helloP abi μ (helloLocs …)`: its owned word `tcbWH` is in its cover set. -/
theorem ownCov1_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w s Lc v, (Lc, v) ∈ wakeOwnXW (tcbM L) (tcbWH L) w 1 s [] →
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).cov 1 Lc :=
  fun w s Lc v h => ownCov1XW _ _ w s Lc v h

/-- The runtime addresses are off every placed label (`flagLdH`'s `hrt`). -/
theorem rt_H : ∀ w a, (msH L G SR w).rt a →
    ¬ ∃ l b, (SR w).lbl l = some b ∧ b ≤ a ∧ a < b + 8 * (SR w).lsize l :=
  fun _ _ h => h

/-- The read side takes every number (`flagLdH`'s `hrdN`; `rd1`). -/
theorem rdN_H : ∀ w (w' : TermRun.Word) n, w'.val = .num n → (msH L G SR w).rd w' :=
  fun _ _ n h => ⟨n, h⟩

/-- `WCompat0.abortAt0` at `PhRec.μ L`. -/
theorem abt_H : ∀ w s, (msH L G SR w).abortAt s →
    ∃ k a, (Spike.Lib.X64.PhRec.μ L).abortAt k = some a ∧ pcOf s = a :=
  fun _ _ h => h

/-- `WCompat0.mpW0` at `Pa := helloP abi μ (helloLocs …)`. -/
theorem mpW_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w Lc, (msHX L G SR w).mp Lc true →
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 0 Lc ∧
        ¬ InLabel (SR w).lbl (SR w).lsize Lc ∧ Consumer1.LocIn L.Λ.shared Lc :=
  fun _ _ h => ⟨.inr (.inl h), (h.1.2 rfl).2, (h.1.2 rfl).1⟩

/-- `WCompat0.noProm0` at `Pa := helloP abi μ (helloLocs …)`. -/
theorem noProm_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w x (t : Thread isa) mem,
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso μ x 0) 0 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => noProm_prom hn hc

end Fields

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}
  {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {D : WSideH ι} {r0 r1 : ι → Range}
  {cw : ι → TermRun.Word}

/-- **`WCompat0` at the placed layout with hello's memory side and location data**: `X64HelloCompatI.hC0P` with
every memory-side fact closed; open: main's pointer word `hcw`. -/
theorem hC0Ms (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hcw : ∀ w, (cw w).val = .loc (cS w) 0) :
    X64WakeM0.WCompat0
      (helloQ arch R1 ι SR cT cS pT
        (fun w => helloP abi (X64HelloCompatI.μP hp i H E asm)
          (helloLocs (RuntimeLayout.ofPlaceWX hp i) (SR w).lbl (SR w).lsize (cT w) (cS w))) G passT
        (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) (msHX (RuntimeLayout.ofPlaceWX hp i) G SR) cw
          (RuntimeLayout.ofPlaceWX hp i).lab (RuntimeLayout.ofPlaceWX hp i).exe (RuntimeLayout.ofPlaceWX hp i).Λ
          (X64HelloCompatI.μP hp i H E asm) (X64HelloCompatI.hoffP hp i hpa))
        D r0 r1)
      (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) (msHX (RuntimeLayout.ofPlaceWX hp i) G SR) cw
        (RuntimeLayout.ofPlaceWX hp i).lab (RuntimeLayout.ofPlaceWX hp i).exe (RuntimeLayout.ofPlaceWX hp i).Λ
        (X64HelloCompatI.μP hp i H E asm) (X64HelloCompatI.hoffP hp i hpa))
      (X64HelloCompatI.μP hp i H E asm) (RuntimeLayout.ofPlaceWX hp i).Λ :=
  X64HelloCompatI.hC0P hp i hpa (K_H (RuntimeLayout.ofPlaceWX hp i) G SR) (G_H (RuntimeLayout.ofPlaceWX hp i) G SR)
    (ownConst_H (RuntimeLayout.ofPlaceWX hp i) G SR) (ownMp_H (RuntimeLayout.ofPlaceWX hp i) G SR)
    (ownCov_H (RuntimeLayout.ofPlaceWX hp i) G SR cT cS) (mpW_H (RuntimeLayout.ofPlaceWX hp i) G SR cT cS)
    (rt_H (RuntimeLayout.ofPlaceWX hp i) G SR) (rdN_H (RuntimeLayout.ofPlaceWX hp i) G SR)
    (abt_H (RuntimeLayout.ofPlaceWX hp i) G SR) hcw (noProm_H (RuntimeLayout.ofPlaceWX hp i) SR cT cS)

end Place

end Spike.Lib.X64HelloMs

/-- info: 'Spike.Lib.X64HelloMs.hC0Ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMs.hC0Ms
