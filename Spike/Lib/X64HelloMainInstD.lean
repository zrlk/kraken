/-
**hello.w on x86-64: main's permit, limit and exit pieces past the clone** (the twin of
`Spike/Lib/HelloMainInstD.lean`): the fields `hlim`, `hT`, `hS`, `htp4`, `hexit` of
`X64HelloMainHRD.MainInstH` at a placed output (`L := RuntimeLayout.ofPlaceWX hp i`), hello's memory side
`X64HelloMs.helloMs L G lbl lsize` (any value invariant `G`, the spawn's placement `lbl`/`lsize`), main's TCB
`tp = L.pinA + 0 + 8`, at a frame `R` with frame condition `DFrame R m0`:

- `rd_numH`: a word `helloMs` reads that represents `1` is the number `1`;
- `hS_IH` (`hS`): the park's store of `0` to `tp + 16` (`X64WakeHS.permit_free`, the word shared,
  `X64WakeMainInstD.locIn_tp16_I`, and in no placed label, `permit_notIn`), given `G` at the word and value
  (`hG`);
- `htp4_IH` (`htp4`): `X64WakeChildSt.childSt_al`;
- `cT_ne_IH`: a flag word in a placed label is not main's limit word (`X64WakeMainInstD.cT_ne_I`);
- `limOk_IH` (`hlim`): the limit load's `LimOk` at `tp + 8` (`X64WakeHS.lim_free`), given `G`'s values at
  the word within the room (`hroom`);
- `hexit_IH` (`hexit`): past the wait loop's load the word read is the number `1` (`rd_numH`), so the
  source's test takes `wlRet`, which returns `0` (`SrcSem.mainExit`);
- `mainInstH_I`: `MainInstH` from the above at the region `⟨Rm.base, -128, 40⟩`.

At hello's root value invariant `wakeG (GOf2H L m0') cT`: `hG_permitH` discharges `hS`'s `hG`, `hroom_limH`
`limOk`'s `hroom` given the flag word not the limit word, which `cT_ne_IH` gives for a flag word in a placed
label; `mainInstH_G` assembles `MainInstH` there.

Open premises: `hA0`/`hoff` per word (`X64WakeMainFlag.hA0_of`/`hAoff_of` at `locIn_tp16_I`, `locIn_tp8_I`,
`locIn_tp0_I`), `hm` (the memory relation at the spawn), `hZ` (the limit load's room bound above stack 0's
guard), and the park's ownership of the TCB word `hown`.

## Differences from the AArch64 version

- No `htls_IH`: the x86-64 wait loop takes the limit's `LimOk` directly (`MainInstH.hlim` at `tp + 8` with
  `Z = (R.fp 8).addr 0 - 8 - 16`), so `limOk_IH` is that field, and `mainInstH_I` asks no source facts
  (`hsh`, `hval`, `hloc`, `hin`) and no `hprog`/`hw`/`hend`.
- `MainInstH` carries x86-64 wake's park facts `hT` and `hown`. `hT` (main's `%fs:0` load at `tp`) is
  discharged here: `tp` is the pinned word `1` (`locIn_tp0_I`), in no placed label (`tp_free`), unloadable in
  the frame (`hA0`, `hoff` at `tp`). `hown` (`OwnAt helloMs … tp tp`) stays open: `helloMs` owns no word
  (`X64HelloQ.helloQ`'s `own` is `X64WakeOwn.wakeOwn`, empty), unlike wake's `msM`, which owns its TCB word.
- `hexit_IH` is `X64WakeMainInstD.hexit_I`'s proof at `helloSrc` and `helloMs` (wake's is stated at
  `wakeSrc`).
- The region is `⟨Rm.base, -128, 40⟩` (AArch64: `⟨Rm.base, -144, 48⟩`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloMainHRD
import Spike.Lib.X64HelloMs
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64WakeMainInstD
import Spike.Lib.X64WakeChildSt

namespace Spike.Lib.X64HelloMainInstD

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep MemRelP Range lrange)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (m0Of pin_ne)
open Spike.Lib.X64HelloMs (helloMs)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainHRD (MainInstH)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (wlIf)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakeMainInstD (unmapped_I pinned_j locIn_tp16_I locIn_tp8_I permit_notIn)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **A word `helloMs` reads representing `1` is the number `1`**. -/
theorem rd_numH {L : RuntimeLayout} {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} (w' : TermRun.Word) (hr : (helloMs L G lbl lsize).rd w')
    (hv : ValRep lbl w'.val 1) : w'.val = .num 1 := by
  obtain ⟨n, hn⟩ := hr
  rw [hn] at hv ⊢
  rw [hv.2]

/-- **`hexit` at the instance**: past the wait loop's load, the word read is the number `1` (`rd_numH`), so
the source's test takes `wlRet`, a placed control whose return is `exit` with code `0`; for any state
predicate `X`. -/
theorem hexit_IH {L : RuntimeLayout} {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {w : TermRun.Word} {X : State → Ctl → Prop} :
    ∀ s c', Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := helloMs L G lbl lsize) lbl) c' → X s c' →
      ¬ (helloMs L G lbl lsize).abortAt s → MainExit helloSrc (helloMs L G lbl lsize) s c' 0 := by
  rintro s c' ⟨w', ⟨hr, hv⟩, rfl⟩ - -
  have h1 := rd_numH w' hr hv
  have ha : TermRun.evalAt (("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env) (.var "d")
      = some (loadTy (.ptr .pub .int), [w']) := by
    simp [TermRun.evalAt, TermRun.lookupE, List.find?]
  have hs := LowerNode.localStep_ifeq (p := helloSrc) (n := 1) (m := 1)
    (c := ⟨wlIf, ("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env, none⟩)
    (ta := loadTy (.ptr .pub .int)) (tb := .intS (.lit 1)) (wb := TermRun.cst (.num 1))
    rfl ha rfl h1 rfl
  rw [ite_eq_left rfl] at hs
  refine ⟨_, .single hs, ⟨fun _ _ => none, ?_, ?_, ?_⟩, ?_⟩
  · intro x ty ws hl k wd wp hk hp
    cases hp
  · intro x hx
    simp [WakeMLive.wlRet, Scc.Sem.exprFv, Scc.Sem.atVars] at hx
  · intro x k n h
    cases h
  · intro s0 th h0 ht he hst
    unfold Scc.Sem.SrcSem.mainExit
    simp only [h0, ht, hst, he]
    rfl

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- Main's TCB is the pinned region's word `1`. -/
theorem tp_eq (L : RuntimeLayout) : L.pinA + 0#64 + 8#64 = L.pinA + BitVec.ofNat 64 (8 * (0 + 1)) := by
  rw [BitVec.add_zero]

/-- **main's TCB word is shared** (`pinned`). -/
theorem locIn_tp0_I : Consumer1.LocIn (Ly).Λ.shared ⟨(Ly).pinA + 0#64 + 8#64, 8⟩ := by
  intro k hk
  rw [tp_eq]
  exact .inr (.inr (pinned_j hp i (j := 1) (by decide) (by decide) k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))

/-- **No placed label covers main's TCB word** (the pinned region's word `1`), as `X64WakeHS.lim_free`. -/
theorem tp_free {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp) :
    ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains ((Ly).pinA + 0#64 + 8#64).toNat := by
  rintro ⟨l, b, hl, hx⟩
  have hc := Scc.Cert.Rt.X64.clear_of_rtOffOk (PlaceWX.rtOff_of_placeWX hp) (j := 1) (by decide)
  have hw := (PlaceWX.wf_link_of_placeWX i hp).inSpace
  have hd := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have hh := hw _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  change Scc.Cert.Rt.X64.clearB (Ly).Λ.data ((Ly).pinA + BitVec.ofNat 64 (8 * (0 + 1))) = true ∧
    Scc.Cert.Rt.X64.clearB (Ly).Λ.heap ((Ly).pinA + BitVec.ofNat 64 (8 * (0 + 1))) = true at hc
  rw [tp_eq] at hx
  have hm' := (Ly).words_small _ ((Ly).fld_mem (i := 0) (by decide))
  have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
  simp only [Scc.Cert.Rt.X64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  simp only [Scc.Sem.Range.contains] at hs
  omega

/-- **`hS` at the instance**: the park's store of `0` to main's permit word `tp + 16` under `helloMs`, in the
frame `R` from `m0`, given the word unloadable there (`hA0`, `hoff`) and `G` of the word at `0` (`hG`). -/
theorem hS_IH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 16#64).toNat))
    (hG : G ⟨tp + 16#64, 8⟩ ((0#64).setWidth 128)) :
    StOk (helloMs (Ly) G lbl lsize) (DFrame R m0) (tp + 16#64) 0#64 := by
  have hu := unmapped_I hA0 hoff
  subst htp
  exact ⟨X64WakeHS.permit_free hp i hm,
    ⟨X64WakeLabMapped.mapped_K0_of_shared (locIn_tp16_I hp i) true,
      fun _ => ⟨locIn_tp16_I hp i, permit_notIn hp i hm⟩⟩, hG, hu⟩

/-- **`htp4` at the instance**: main's permit word is 4-aligned. -/
theorem htp4_IH {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64) : (tp + 16#64).toNat % 4 = 0 := by
  subst htp
  rw [show (Ly).pinA + 0#64 + 8#64 + 16#64 = (Ly).pinA + 24#64 by bv_omega]
  exact X64WakeChildSt.childSt_al hp i

/-- **The flag's target word is not main's limit word**: a flag word in a placed label (`hl`, `ho`, `hT`) is
not `tp + 8`, which is in none (`X64WakeMainInstD.cT_ne_I`). -/
theorem cT_ne_IH {cT : Loc} {cS : WeakMem.Address} {b : Nat} (hl : lbl cS.label = some b)
    (ho : cS.offset < lsize cS.label) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp) :
    (⟨(Ly).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT :=
  X64WakeMainInstD.cT_ne_I hp i hm hl ho hT

/-- **The limit load's `LimOk` at the instance**: main's limit word `tp + 8` under `helloMs`, in the frame `R`
from `m0` (`hA0`, `hoff` as `hS_IH`'s), with `G`'s values at the word within the room up to `Z` (`hroom`). -/
theorem limOk_IH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 8#64).toNat))
    {Z : BitVec 64} (hroom : ∀ v : Val, G ⟨tp + 8#64, 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat) :
    LimOk (helloMs (Ly) G lbl lsize) (DFrame R m0) (tp + 8#64) Z := by
  have hu := unmapped_I hA0 hoff
  subst htp
  exact ⟨X64WakeHS.lim_free hp i hm, ⟨X64WakeLabMapped.mapped_K0_of_shared (locIn_tp8_I hp i) false, nofun⟩,
    hu, hroom⟩

/-- **`MainInstH` at the instance** (`limOk_IH`, `hS_IH`, `htp4_IH`, `hexit_IH`, the TCB load from
`locIn_tp0_I`/`tp_free`, at the region `⟨Rm.base, -128, 40⟩`): `G` at the permit word (`hG`), the limit
word's values within the room up to the wait loop's bound (`hroom`), and the park's ownership `hown` open. -/
theorem mainInstH_I {exe : _root_.Executable} {endPc : Int64}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp)
    {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64)
    {Rm : Region} {m0 : MachineData}
    (hA0 : Mem.loadInt m0.dmem tp 8 = none)
    (hoff0 : tp.toNat + 8 ≤ 2 ^ 64 ∧
      ((tp.toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ tp.toNat))
    (hA16 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff16 : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ (tp + 16#64).toNat))
    (hA8 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff8 : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ (tp + 8#64).toNat))
    (hG : G ⟨tp + 16#64, 8⟩ ((0#64).setWidth 128))
    (hroom : ∀ v : Val, G ⟨tp + 8#64, 8⟩ v →
      (v.setWidth 64).toNat ≤ (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    (hown : OwnAt (helloMs (Ly) G lbl lsize) exe endPc
      ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    {w : TermRun.Word} :
    MainInstH exe endPc lbl (helloMs (Ly) G lbl lsize) m0 Rm tp w where
  hlim := by
    rw [show (8 : Int64).toBitVec = 8#64 by decide]
    exact limOk_IH hp i hm htp (R := ⟨Rm.base, -128, 40⟩) hA8 hoff8 hroom
  hT := by
    have hu := unmapped_I (R := ⟨Rm.base, -128, 40⟩) hA0 hoff0
    subst htp
    exact ⟨tp_free hp i hm, ⟨X64WakeLabMapped.mapped_K0_of_shared (locIn_tp0_I hp i) false, nofun⟩, hu⟩
  hown := hown
  hS := hS_IH hp i hm htp (R := ⟨Rm.base, -128, 40⟩) hA16 hoff16 hG
  htp4 := htp4_IH hp i htp
  hexit := fun s c h hX => hexit_IH s c h hX

/-! ## At hello's root value invariant `wakeG (GOf2H L m0') cT` -/

/-- **`G` at main's permit word** under `wakeG (GOf2H L m0') cT`, any value (`hS_IH`'s `hG`): the word is
neither limit word. -/
theorem hG_permitH {m0' : Memory} {cT : Loc} {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64) (v : Val) :
    WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) m0') cT ⟨tp + 16#64, 8⟩ v := by
  subst htp
  refine .inr ?_
  rw [X64WakeHS.permit_eq]
  exact X64HelloGOf2H.gOf2H_ne (pin_ne (by decide)) (X64HelloGOf2H.pin_ne2H (by decide)) _

/-- **The limit word's values within the room** under `wakeG (GOf2H L (m0Of …)) cT`, for any `Z` at least
stack 0's limit (`hZ`), the flag word not the limit word (`hcT`; `cT_ne_IH`): `limOk_IH`'s `hroom`. -/
theorem hroom_limH {cT : Loc} {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64)
    (hcT : (⟨(Ly).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT)
    {Z : BitVec 64} (hZ : (Ly).stacksA.toNat + 4096 ≤ Z.toNat) :
    ∀ v : Val, WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs)) cT ⟨tp + 8#64, 8⟩ v →
      (v.setWidth 64).toNat ≤ Z.toNat := by
  subst htp
  intro v hv
  have hg' := Spike.Lib.WakeG.wakeG_off hv hcT
  rw [X64WakeHS.lim_eq, ← Spike.Lib.X64.Rt.limA_tcb0] at hg'
  exact PlaceWX.room_of_le hp i hZ v (X64HelloGOf2H.gOf_of_gOf2H hg')

/-- **`MainInstH` at hello's root value invariant** `wakeG (GOf2H L (m0Of …)) cT` (`mainInstH_I` with
`hG_permitH`, `hroom_limH`; the flag word `cT` in a placed label at `cS`, `hl`/`ho`/`hT`; the wait loop's
room bound above stack 0's guard, `hZ`). -/
theorem mainInstH_G {exe : _root_.Executable} {endPc : Int64}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tq0 tq sp)
    {cT : Loc} {cS : WeakMem.Address} {b : Nat} (hl : lbl cS.label = some b)
    (ho : cS.offset < lsize cS.label) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    {tp : BitVec 64} (htp : tp = (Ly).pinA + 0#64 + 8#64)
    {Rm : Region} {m0 : MachineData}
    (hA0 : Mem.loadInt m0.dmem tp 8 = none)
    (hoff0 : tp.toNat + 8 ≤ 2 ^ 64 ∧
      ((tp.toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ tp.toNat))
    (hA16 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff16 : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ (tp + 16#64).toNat))
    (hA8 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff8 : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ Rm.base.toNat + -128 ∨ (Rm.base.toNat : Int) + 40 ≤ (tp + 8#64).toNat))
    (hZ : (Ly).stacksA.toNat + 4096 ≤
      (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    (hown : OwnAt (helloMs (Ly) (WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs)) cT)
        lbl lsize) exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    {w : TermRun.Word} :
    MainInstH exe endPc lbl
      (helloMs (Ly) (WakeG.wakeG (X64HelloGOf2H.GOf2H (Ly) (m0Of (Ly).Λ o.prog o.secs)) cT) lbl lsize)
      m0 Rm tp w :=
  mainInstH_I hp i hm htp hA0 hoff0 hA16 hoff16 hA8 hoff8 (hG_permitH hp i htp _)
    (hroom_limH hp i htp (cT_ne_IH hp i hl ho hT hm) hZ) hown

end Inst

end Spike.Lib.X64HelloMainInstD

/-- info: 'Spike.Lib.X64HelloMainInstD.rd_numH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.rd_numH

/-- info: 'Spike.Lib.X64HelloMainInstD.hexit_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.hexit_IH

/-- info: 'Spike.Lib.X64HelloMainInstD.tp_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.tp_free

/-- info: 'Spike.Lib.X64HelloMainInstD.locIn_tp0_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.locIn_tp0_I

/-- info: 'Spike.Lib.X64HelloMainInstD.hS_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.hS_IH

/-- info: 'Spike.Lib.X64HelloMainInstD.htp4_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.htp4_IH

/-- info: 'Spike.Lib.X64HelloMainInstD.cT_ne_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.cT_ne_IH

/-- info: 'Spike.Lib.X64HelloMainInstD.limOk_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.limOk_IH

/-- info: 'Spike.Lib.X64HelloMainInstD.mainInstH_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.mainInstH_I

/-- info: 'Spike.Lib.X64HelloMainInstD.hG_permitH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.hG_permitH

/-- info: 'Spike.Lib.X64HelloMainInstD.hroom_limH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.hroom_limH

/-- info: 'Spike.Lib.X64HelloMainInstD.mainInstH_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInstD.mainInstH_G
