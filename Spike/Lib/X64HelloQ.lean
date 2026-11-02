/-
**hello.w on x86-64: the concrete relation data** (the twin of
`Spike.Lib.X64WakeQ` at hello's worker side `X64HelloW1.WSideH`). `helloQ` fixes
the fields of `WakeRel` that hello's assembly pins by an equation, so that
each of those equations is `rfl`:

- `PT0 := X64WakeM0.PT0 M` (`hPT0`; main's side past the spawn is wake's),
  `KR := X64HelloKRE.KRHE D r0 r1` (`hKR`; `X64HelloWriteK.KRH` (no `exit` in the
  source trace in place of an empty trace) and the worker's `write` link `Lk`,);
- `own w i s fs := if i = 0 then (M.ms w).own s else (D.ms w fs).own s`: the owned words are read off the
  memory sides (`own_zero`, `own_one`), so `WCompat0.own0` holds by `rfl` and `WCompatH.ownCov`/`ownDisj`
  (`ownCov`, `ownDisj`) are the sides' facts. They are `rfl`/side facts only because the content (which words are
  owned, that they are constant, covered and never a runtime write's target) moves to the instance: the sides'
  self words (wake's `X64WakeOwnX.wakeOwnXW` at hello's TCB words, `own_XW`, at the instance
  `X64HelloAssemblyI.own_QH`) and the worker rows' `X64HelloOwn1.Own1H`;
- `PT1 := X64HelloEmitPh.PT1hE D` (`WCompatH.pt1`; `PT1h` or mid-`write`),
  `atUnpk := X64WakeW1.atUnpk`,
  `atTexit := X64WakeW1.atTexit` (hello's worker tail is wake's);
- `C w := helloC (cT w) (cS w) passT Knobs.all arch (D.cw w)`, so
  `WCompatH.C` and `hpT` hold by `rfl`; `mviewS`, `obS` are `helloC`'s, the
  real `Promises.storeMview`/`storeOb` of the worker's `store rel c 1` (the
  review guard of `WakeRel.C`).

The target store point `passT` is a parameter (hello's listing places the
worker's `stlr` at its own labels; `X64WakeQ` fixes wake's `wakePassT`). The
rest (`R1`, `ι`, `SR`, the flag's words `cT`/`cS`, `pT`, `P`, `G`) are
parameters, as in `X64WakeQ`.

x86-64 twin of `Spike/Lib/HelloQ.lean` (same names, namespaces with the `X64` prefix).
-/
import Spike.Lib.X64WakeQ
import Spike.Lib.X64HelloW1Print
import Spike.Lib.X64HelloWriteK
import Spike.Lib.X64HelloKRE

namespace Spike.Lib.X64HelloQ

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WorkerSrc
open Spike.Lib.X64HelloW1 (WSideH PT1h)

/-- **hello's relation data**: the pinned fields fixed, the rest given. -/
def helloQ (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (ι : Type) (SR : ι → SpawnRec)
    (cT : ι → Loc) (cS : ι → WeakMem.Address) (pT : ι → Loc) (P : ι → Inv2Params isa)
    (G : ι → Loc → Val → Prop) (passT : State → Prop) (M : X64WakeM0.MSide ι) (D : WSideH ι)
    (r0 r1 : ι → Range) : WakeRel where
  R1 := R1
  ι := ι
  SR := SR
  C w := helloC (cT w) (cS w) passT Promises.Knobs.all arch (D.cw w)
  pT := pT
  P := P
  G := G
  own w i s fs := if i = 0 then (M.ms w).own s else (D.ms w fs).own s
  PT0 := X64WakeM0.PT0 M
  PT1 := X64HelloEmitPh.PT1hE D
  KR := X64HelloKRE.KRHE D r0 r1
  atUnpk := X64WakeW1.atUnpk
  atTexit := X64WakeW1.atTexit

section Rfl

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {ι : Type} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {P : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range}

/-- The pinned fields of `helloQ`, each `rfl`. -/
theorem hPT0 : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT0 = X64WakeM0.PT0 M := rfl
/-- **`WCompatH.ownCov`** at `helloQ`: the worker's owned words are its side's, in its cover set when the
side's are (`hcov`). -/
theorem ownCov (hcov : ∀ w s fs L v, (L, v) ∈ (D.ms w fs).own s → (P w).cov 1 L) :
    ∀ w s fs L v, (L, v) ∈ (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 1 s fs →
    ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).P w).cov 1 L := hcov

/-- **`WCompatH.ownDisj`** at `helloQ`: main's owned words are its side's, the worker's its side's, disjoint
when the sides' are (`hdisj`). -/
theorem ownDisj (hdisj : ∀ w s0 s fs L v v', (L, v) ∈ (M.ms w).own s0 → (L, v') ∈ (D.ms w fs).own s → False) :
    ∀ w s0 fs0 s fs L v v',
    (L, v) ∈ (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 0 s0 fs0 →
    (L, v') ∈ (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 1 s fs → False :=
  fun w s0 _ s fs L v v' h0 h1 => hdisj w s0 s fs L v v' h0 h1

/-- **The owned words read off the sides**: thread `0`'s are main's side's, thread `1`'s the worker's. -/
theorem own_zero (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 0 s fs = (M.ms w).own s := rfl

/-- See `own_zero`. -/
theorem own_one (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 1 s fs = (D.ms w fs).own s := rfl

/-- **The owned words are wake's self words** `wakeOwnXW T W` when main's side owns `T`'s word alone and the
worker's side `W`'s (`X64HelloSpawnR.spawn_RH`'s `post_startH`; at the instance `X64HelloAssemblyI.own_QH`). -/
theorem own_XW {T W : BitVec 64} (h0 : ∀ w s, (M.ms w).own s = [(⟨T, 8⟩, T.setWidth 128)])
    (h1 : ∀ w s fs, (D.ms w fs).own s = [(⟨W, 8⟩, W.setWidth 128)]) :
    (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own = X64WakeOwnX.wakeOwnXW T W := by
  funext w i s fs
  show (if i = 0 then (M.ms w).own s else (D.ms w fs).own s) =
    if i = 0 then [(⟨T, 8⟩, T.setWidth 128)] else [(⟨W, 8⟩, W.setWidth 128)]
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]; exact h0 w s
  · rw [if_neg hi, if_neg hi]; exact h1 w s fs

/-- **`WCompatH.pt0`** at `helloQ`: main's `PT0` does not read the memories
(`X64WakeM0.PT0.mem`). -/
theorem pt0 : ∀ w tm sm t0 s0 tm' sm', (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT0 w tm sm t0 s0 →
    X64WakeW1.W1Mem ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).P w)
      ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).cS tm sm tm' sm' →
    (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT0 w tm' sm' t0 s0 :=
  fun _ _ _ _ _ _ _ h _ => h

end Rfl

end Spike.Lib.X64HelloQ

/-- info: 'Spike.Lib.X64HelloQ.own_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.own_zero

/-- info: 'Spike.Lib.X64HelloQ.own_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.own_one

/-- info: 'Spike.Lib.X64HelloQ.own_XW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.own_XW


/-- info: 'Spike.Lib.X64HelloQ.hPT0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.hPT0

/-- info: 'Spike.Lib.X64HelloQ.ownCov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.ownCov

/-- info: 'Spike.Lib.X64HelloQ.ownDisj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.ownDisj

/-- info: 'Spike.Lib.X64HelloQ.pt0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloQ.pt0
