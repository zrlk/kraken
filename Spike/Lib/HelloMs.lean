/-
**hello.w on AArch64: both threads' memory side and location data at a
placed output** (the twin of `WakeInst.wakeMs` / `wakeLocs` and of their
`WCompat0` field lemmas, at hello's records: any runtime layout `L`, value
invariant `G`, placement `lbl`/`lsize`).

- `helloMs L G lbl lsize`: the consumer's `msOf` at read side the numbers
  (`∃ n, w.val = .num n`), value invariant `G`, no owned word, the
  placement, with its runtime writes narrowed to words outside every placed
  label (as `wakeMs`, at `L`'s layout and marks `PhRec.μ L`).
- `helloLocs L lbl lsize cT cS`: no owned word, each thread's other
  footprint the words `helloMs` lets it write; `helloLocs_ok`.
- The memory side's facts `HelloCompat0.hC0H` / `HelloCompatI.hC0P` read:
  `K_H`, `G_H`, `own_H`, `rt_H`, `rdN_H`, `abt_H`, and `mpW_H` (the
  footprint at `Pa := HelloInst.helloP abi μ (helloLocs …)`), `noProm_H`.
- `hC0Ms`: `HelloCompatI.hC0P` at `ms := helloMs L (G w) (SR w).lbl
  (SR w).lsize`, `Pa := helloP abi μP (helloLocs …)`; open: main's pointer
  word `hcw`.
-/
import Spike.Lib.HelloCompatI
import Spike.Lib.A64HelloInst

namespace Spike.Lib.HelloMs

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeP
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (msOf K0)
open Spike.Lib.HelloMainInv (helloM)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.HelloInst (helloP)

/-- **Both threads' memory side** (see the module doc). -/
def helloMs (L : RuntimeLayout) (G : Loc → Val → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) : MemSide isaLSE2 :=
  { msOf L.Λ (Spike.Lib.A64.PhRec.μ L) (fun w => ∃ n, w.val = .num n) G (fun _ => []) lbl lsize with
    mp := fun Lc w => Scc.Sem.Kernel.mapped (K0 L.Λ) w Lc = true ∧
      (w = true → Consumer1.LocIn L.Λ.shared Lc ∧ ¬ InLabel lbl lsize Lc) }

/-- **The location data**: no owned word; each thread's other footprint
words the runtime words `helloMs` lets it write. -/
def helloLocs (L : RuntimeLayout) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (cT : Loc) (cS : WeakMem.Address) : WakeLocs where
  lbl := lbl
  lsize := lsize
  cT := cT
  cS := cS
  own _ _ := False
  priv _ Lc := (helloMs L (fun _ _ => True) lbl lsize).mp Lc true

/-- `helloLocs`' separation facts. -/
theorem helloLocs_ok (L : RuntimeLayout) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (cT : Loc) (cS : WeakMem.Address) : (helloLocs L lbl lsize cT cS).OK where
  disj _ _ _ _ _ _ _ h := h
  own_nlab _ _ _ h := h.elim
  priv_nlab _ _ _ h := (h.2 rfl).2
  c_own h := h

section Fields

variable {ι : Type} (L : RuntimeLayout) (G : ι → Loc → Val → Prop) (SR : ι → SpawnRec)

/-- The memory side at record `w`. -/
abbrev msH (w : ι) : MemSide isaLSE2 := helloMs L (G w) (SR w).lbl (SR w).lsize

/-- `WCompat0.K0`. -/
theorem K_H : ∀ w, (msH L G SR w).K = some abi := fun _ => rfl

/-- `WCompat0.G0`. -/
theorem G_H : ∀ w, (msH L G SR w).G = G w := fun _ => rfl

/-- `WCompat0.own0`. -/
theorem own_H : ∀ w s, (msH L G SR w).own s = [] := fun _ _ => rfl

/-- The runtime addresses are off every placed label (`flagLdH`'s `hrt`). -/
theorem rt_H : ∀ w a, (msH L G SR w).rt a →
    ¬ ∃ l b, (SR w).lbl l = some b ∧ b ≤ a ∧ a < b + 8 * (SR w).lsize l :=
  fun _ _ h => h

/-- The read side takes every number (`flagLdH`'s `hrdN`; `rd1`). -/
theorem rdN_H : ∀ w (w' : TermRun.Word) n, w'.val = .num n → (msH L G SR w).rd w' :=
  fun _ _ n h => ⟨n, h⟩

/-- `WCompat0.abortAt0` at `PhRec.μ L`. -/
theorem abt_H : ∀ w s, (msH L G SR w).abortAt s →
    ∃ k a, (Spike.Lib.A64.PhRec.μ L).abortAt k = some a ∧ pcOf s = a :=
  fun _ _ h => h

/-- `WCompat0.mpW0` at `Pa := helloP abi μ (helloLocs …)`. -/
theorem mpW_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w Lc, (msH L G SR w).mp Lc true →
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 0 Lc ∧
        ¬ InLabel (SR w).lbl (SR w).lsize Lc ∧ Consumer1.LocIn L.Λ.shared Lc :=
  fun _ _ h => ⟨.inr (.inl ⟨h.1, h.2⟩), (h.2 rfl).2, (h.2 rfl).1⟩

/-- `WCompat0.noProm0` at `Pa := helloP abi μ (helloLocs …)`. -/
theorem noProm_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w x (t : Thread isaLSE2) mem,
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 0) 0 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => noProm_prom hn hc

end Fields

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String}
  {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {D : WSideH ι} {r0 r1 : ι → Range}
  {cw : ι → TermRun.Word}

/-- **`WCompat0` at the placed layout with hello's memory side and location
data**: `HelloCompatI.hC0P` with every memory-side fact closed; open: main's
pointer word `hcw`. -/
theorem hC0Ms (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hcw : ∀ w, (cw w).val = .loc (cS w) 0) :
    WakeM0.WCompat0
      (helloQ arch R1 ι SR cT cS pT
        (fun w => helloP abi (HelloCompatI.μP hp i H E asm)
          (helloLocs (RuntimeLayout.ofPlaceW hp i) (SR w).lbl (SR w).lsize (cT w) (cS w))) G passT
        (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) (msH (RuntimeLayout.ofPlaceW hp i) G SR) cw
          (RuntimeLayout.ofPlaceW hp i).lab (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ
          (HelloCompatI.μP hp i H E asm) (HelloCompatI.hoffP hp i hpa))
        D r0 r1)
      (helloM (fun w => (SR w).lbl) (fun w => (SR w).lsize) (msH (RuntimeLayout.ofPlaceW hp i) G SR) cw
        (RuntimeLayout.ofPlaceW hp i).lab (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ
        (HelloCompatI.μP hp i H E asm) (HelloCompatI.hoffP hp i hpa))
      (HelloCompatI.μP hp i H E asm) (RuntimeLayout.ofPlaceW hp i).Λ :=
  HelloCompatI.hC0P hp i hpa (K_H _ G SR) (G_H _ G SR) (own_H _ G SR) (mpW_H _ G SR cT cS) (rt_H _ G SR)
    (rdN_H _ G SR) (abt_H _ G SR) hcw (noProm_H _ SR cT cS)

end Place

end Spike.Lib.HelloMs

/-- info: 'Spike.Lib.HelloMs.hC0Ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMs.hC0Ms
