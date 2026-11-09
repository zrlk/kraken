/-
**hello's root base's layout fields from `PlaceWX`** (x86-64; twin of `Spike/Lib/A64HelloRootPlug.lean`):
`HelloRootBase`'s fields that are facts of `PlaceWX`'s layout `RuntimeLayout.ofPlaceWX hpw (immsH Λ0 i0)`, from the
loader's facts the root carries (the program's two parses, the code base, A13's data part `hA13`), as wake's
`StartPlaceLy`, `WakeOSide`, `StartH0Ti`, `Ti2Fld` plug wake's.

- `hpo_H`, `hp_H`, `hlo_H`, `hΛ_H`, `hlab_H`, `hsite_H`: the program, the code base, the abort labels, the labels
  and the take site (`siteH`).
- `hro_H`, `hs_H`, `hsub_H`: `.rodata` off the stack pool (A1), the words' separation at `scc_rt_nthreads` and the
  second stack in the pool (A13's data part).
- `tiH_word`, `tiH_spawn`: the second TCB `tH = pinA + 144` is `spawnWords`' words `4` to `9`.
- `hmF_H`, `hnoF_H`, `hoffT_H`: the second TCB's words mapped (A13's data part: in `.data` or `pinned`), none of
  `own2bH`'s, off `arW` (`H2Rt.hoffSp_H`).
- `hoffL_H`, `hoffX_H`: the stack lock and cursor off `arW` (`HrdArena.offW_arWH`).
- `hK2_H`, `hpub2_H`: `h2`'s side `ms2H`'s kernel and publication (`rfl`, `arW`'s `pub`).
- `RootRest`, `RootRest.toBase`: the base's fields not plugged here (`Dt`, `Ctx`, `ls`, `frM`, `msB`, `F0`, `hokb`,
  `hg`), and the base from them, `har` by `HelloRootBase.har_W` and the loader facts `hpa`, `hhp`, `hlo0`,
  `hA13`, `CtrZ`.

## Unlike AArch64

- The loader's parses are `Scc.Sem.X64.cellsOf asm = some …` at an x86-64 `Asm` (AArch64
  `textProgram asm = .ok …` at a `String`), the program is `helloCells` and the labels are `codeLabel`'s.
- The stack lock and cursor are off `arW` by `HrdArena.offW_arWH` at their `rtWords` membership (AArch64
  `StartH0Ti.offW_arW`); x86-64 has no separate `offW_arW`.
-/
import Spike.Lib.X64HelloRootInst
import Spike.Lib.X64HelloStart
import Spike.Lib.X64HelloOwn2
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64HelloH2Rt
import Spike.Lib.X64HelloHrdOff
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeStartPlaceLy

namespace Spike.Lib.X64.HelloPh.RootPlug

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.Flow.HelloWc (tH)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open CoreLang CoreTerm
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64.Alloc (Call)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW hpw IH

section Code

variable {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
  (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)

include hpa hhp in
/-- **The output's program is hello's**, from the loader's two parses of the certificate. -/
theorem hpo_H : o.prog = SccCode.helloCells :=
  Option.some.inj (hpa.symm.trans hhp)

include hpa hhp in
/-- **`hp`**: the layout's program is hello's. -/
theorem hp_H : (Ly).prog = SccCode.helloCells :=
  hpo_H hpa hhp

include hlo0 in
/-- **`hlo`**: the code's base is the input layout's. -/
theorem hlo_H : (Ly).Λ.code.lo = lo :=
  hlo0

/-- **`hΛ`**: the runtime's abort labels (`PlaceWX`'s). -/
theorem hΛ_H : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
  Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)

include hpa hhp hlo0 in
/-- **`hlab`**: the layout's labels are hello's code offsets at `lo` (`X64HelloOInit.hlab_H` at `IH`). -/
theorem hlab_H : ∀ l x, codeLabel lo SccCode.helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
  Spike.Lib.X64HelloOInit.hlab_H hpw IH hpa hhp hlo0

include hpa hhp hlo0 in
/-- **`hsite`**: the take site at its label (`siteH`). -/
theorem hsite_H :
    (Spike.Lib.X64.PhRec.μ (Ly)).site .take =
      some ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat :=
  siteH (hp_H hpw i0 hpa hhp) (hlo_H hpw i0 hlo0) (hlab_H hpw i0 hpa hhp hlo0)

end Code

/-- **`hro`**: `.rodata` off the stack pool (A1; wake's `WakeOSide.hro_W`). -/
theorem hro_H : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool :=
  Spike.Lib.X64WakeOSide.hro_W hpw IH

section A13

variable (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)

include hA13

/-- **`hs`**: the runtime's words separated at `scc_rt_nthreads` (wake's `StartPlaceLy.wsep_W`). -/
theorem hs_H : Spike.Lib.X64.WakePh.WSep (Ly) (ntA (Ly).lab) :=
  Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13

/-- **`hsub`**: the second stack in the pool (wake's `StartPlaceLy.hsub1_W`). -/
theorem hsub_H : (r1Of (Ly).lab).Sub (Ly).Λ.stackPool :=
  Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hpw IH hA13

omit hA13 in
/-- **A word of the second TCB** `tH = pinA + 144` is `pinA + 112 + 8 (4 + k)`, `spawnWords`' word `4 + k`. -/
theorem tiH_word {a : BitVec 64} (ha : a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH (Ly).lab)) :
    ∃ k < 6, a = (Ly).pinA + BitVec.ofNat 64 (112 + 8 * (4 + k)) := by
  have e : ∀ c : Nat, tH (Ly).lab + BitVec.ofNat 64 c = (Ly).pinA + BitVec.ofNat 64 (144 + c) := fun c => by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 144#64 + BitVec.ofNat 64 c = _
    rw [(Ly).lab_pin, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  simp only [Spike.Lib.X64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, e _⟩
  · exact ⟨1, by decide, e _⟩
  · exact ⟨2, by decide, e _⟩
  · exact ⟨3, by decide, e _⟩
  · exact ⟨4, by decide, e _⟩
  · exact ⟨5, by decide, e _⟩

omit hA13 in
/-- The second TCB's words are `spawnWords`'. -/
theorem tiH_spawn {a : BitVec 64} (ha : a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH (Ly).lab)) :
    a ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA := by
  obtain ⟨k, hk, rfl⟩ := tiH_word hpw i0 ha
  exact List.mem_map.2 ⟨4 + k, List.mem_range.2 (by simp only [Scc.IR.Tcb.size, Scc.IR.maxSpawnArgs]; omega), rfl⟩

/-- **`hmF`**: the second TCB's words mapped for a write (A13's data part: their bytes in `.data` or `pinned`). -/
theorem hmF_H : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH (Ly).lab),
    Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) true ⟨a, 8⟩ = true := fun a ha =>
  Spike.Lib.X64Consumer.mapped_K0_of_mem
    ((Spike.Lib.X64.WakePh.H1Rt.a13_facts hpw IH hA13).2.1 a (tiH_spawn hpw i0 ha))

/-- **`hnoF`**: the second TCB's words are none of `own2bH`'s (A13's data part: `spawnWords` apart from the
runtime's words and from `scc_rt_nthreads`; wake's `Ti2Fld.hnoF2_W`). -/
theorem hnoF_H : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH (Ly).lab), ∀ j w,
    (⟨b, 8⟩, w) ∉ own2bH (Ly) (ntA (Ly).lab) j := by
  intro a ha j w hw
  have hw' : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab] := by
    simp only [own2bH, Spike.Lib.X64.WakePh.ownV, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h <;>
      (have e := congrArg (fun x : Loc × Val => x.1.addr) h; simp only [] at e; rw [e]; simp)
  have hm := tiH_spawn hpw i0 ha
  have hA := Spike.Lib.X64.WakePh.H1Rt.a13_facts hpw IH hA13
  have hO : ∀ y ∈ (Ly).rtWords, a ≠ y := hA.2.2.2.2 a hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with h | h | h | h | h
  · exact hO _ (Ly).pn_mem h
  · exact hO _ (Ly).lock_mem h
  · exact hO _ (Ly).freeN_mem h
  · exact hO _ (Ly).next_mem h
  · exact hA.2.2.2.1 a hm h.symm

/-- **`hoffT`**: the second TCB's words off `arW` (`H2Rt.hoffSp_H`, at `spawnWords`). -/
theorem hoffT_H : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH (Ly).lab),
    ¬ ((AW).heap ≤ b.toNat ∧ b.toNat < (AW).heap + 16 * (AW).cells) ∧ (⟨b, 8⟩ : Loc) ≠ (AW).ctrLoc :=
  fun _ hb => Spike.Lib.X64.HelloPh.H2Rt.hoffSp_H hpw IH hA13 (tiH_spawn hpw i0 hb)

end A13

/-- **`hoffL`**: the stack lock off `arW` (`HrdArena.offW_arWH` at `lock_mem`). -/
theorem hoffL_H : ¬ ((AW).heap ≤ (Ly).lockA.toNat ∧ (Ly).lockA.toNat < (AW).heap + 16 * (AW).cells) ∧
    (⟨(Ly).lockA, 8⟩ : Loc) ≠ (AW).ctrLoc :=
  Spike.Lib.X64.HelloPh.HrdArena.offW_arWH hpw i0 _ (Ly).lock_mem

/-- **`hoffX`**: the stack cursor off `arW` (`HrdArena.offW_arWH` at `next_mem`). -/
theorem hoffX_H : ¬ ((AW).heap ≤ (Ly).nextA.toNat ∧ (Ly).nextA.toNat < (AW).heap + 16 * (AW).cells) ∧
    (⟨(Ly).nextA, 8⟩ : Loc) ≠ (AW).ctrLoc :=
  Spike.Lib.X64.HelloPh.HrdArena.offW_arWH hpw i0 _ (Ly).next_mem

/-- **`hK2`**: `h2`'s side `ms2H` has the ABI's kernel at no frames (`msOfA`'s, by `rfl`). -/
theorem hK2_H (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n' →
      (Spike.Lib.X64.HelloPh.H2Rt.ms2H asm hpw IH E ls l b n l' b' n' []).K = some Scc.Sem.X64.abi :=
  fun _ _ _ _ _ _ _ => rfl

/-- **`hpub2`**: `h2`'s side `ms2H` admits the source's publication (`arW`'s `pub`). -/
theorem hpub2_H (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b n l' b' n' →
      (Spike.Lib.X64.HelloPh.H2Rt.ms2H asm hpw IH E ls l b n l' b' n' []).pub :=
  fun _ _ _ _ _ _ _ => trivial

/-! ## The base from its rest -/

/-- **`HelloRootBase`'s fields this module does not plug** (the rest: the start's level's choices, the box's side
and frame, the carry to `h2`'s side). -/
structure RootRest (L : RuntimeLayout) (lbl : Lbl) (ar : Spike.Lib.Arena)
    (ms2 : Spike.Lib.X64Consumer.Lsize → WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
      List TermRun.Frame → Spike.Lib.MemSide isa) : Type where
  /-- The start's level's debts (`StartWf.WSH`'s `Dt`). -/
  Dt : State → Prop
  /-- The start's level's contexts (`WSH`'s `Ctx`). -/
  Ctx : Spike.Lib.FragS isa
  /-- The start's sizes, raw (`HelloRootBase.ls`; every use at `WakeLoadT.ls0T ls`). -/
  ls : Spike.Lib.X64Consumer.Lsize
  /-- main's frame (`HelloRootBase.frM`). -/
  frM : TermRun.Frame
  /-- The memory side the box's landing is stated at, per rodata's allocation (hello's box lands in `h1`'s
  segment, so the instance is `h1`'s side at no frames). -/
  msB : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.MemSide isa
  /-- The box's frame condition. -/
  F0 : MachineData → Prop
  /-- The box call's premises carry from `msB` to `h2`'s side. -/
  hokb : ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H ar lbl l b n l' b' n' →
    ∀ q : Call, q.OKB (msB l b n) L.lab → q.OKB (ms2 ls l b n l' b' n' []) L.lab
  /-- `h2`'s arena geometry `msB`'s. -/
  hg : ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H ar lbl l b n l' b' n' →
    (ms2 ls l b n l' b' n' []).heap = (msB l b n).heap ∧
      (ms2 ls l b n l' b' n' []).cells = (msB l b n).cells ∧
      (ms2 ls l b n l' b' n' []).off = (msB l b n).off ∧
      (ms2 ls l b n l' b' n' []).units = (msB l b n).units

/-- **The base from its rest** at `PlaceWX`'s layout, `arW` and `ms2H`: the layout fields by this module, `har` by
`HelloRootBase.har_W` (`CtrZ`), `hK2`/`hpub2` at `ms2H`; the loader facts are the program's two parses (`hpa`,
`hhp`), the code base (`hlo0`), A13's data part (`hA13`) and the counter's zeroed item (`hc`). -/
noncomputable def RootRest.toBase (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry)
    (B : RootRest (Ly) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (AW) (Spike.Lib.X64.HelloPh.H2Rt.ms2H asm hpw IH E))
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hc : Spike.Lib.X64.Rt.CtrZ o) :
    Spike.Lib.X64.HelloPh.HelloRootBase (Ly) (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (AW)
      (Spike.Lib.X64.HelloPh.H2Rt.ms2H asm hpw IH E) where
  hp := hp_H hpw i0 hpa hhp
  hlo := hlo_H hpw i0 hlo0
  hΛ := hΛ_H hpw i0
  hlab := hlab_H hpw i0 hpa hhp hlo0
  hsite := hsite_H hpw i0 hpa hhp hlo0
  hro := hro_H hpw i0
  har := Spike.Lib.X64.HelloPh.HelloRootBase.har_W hpw i0 hc
  Dt := B.Dt
  Ctx := B.Ctx
  ls := B.ls
  frM := B.frM
  msB := B.msB
  F0 := B.F0
  hK2 := hK2_H hpw i0 asm E B.ls
  hpub2 := hpub2_H hpw i0 asm E B.ls
  hokb := B.hokb
  hg := B.hg
  hs := hs_H hpw i0 hA13
  hsub := hsub_H hpw i0 hA13
  hmF := hmF_H hpw i0 hA13
  hnoF := hnoF_H hpw i0 hA13
  hoffT := hoffT_H hpw i0 hA13
  hoffL := hoffL_H hpw i0
  hoffX := hoffX_H hpw i0

end Spike.Lib.X64.HelloPh.RootPlug

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hpo_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hpo_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hp_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hp_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hlo_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hlo_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hΛ_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hΛ_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hlab_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hlab_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hsite_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hsite_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hro_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hro_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hs_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hs_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hsub_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hsub_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.tiH_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.tiH_word

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.tiH_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.tiH_spawn

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hmF_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hmF_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hnoF_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hnoF_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hoffT_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hoffT_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hoffL_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hoffL_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hoffX_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hoffX_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hK2_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hK2_H

/-- info: 'Spike.Lib.X64.HelloPh.RootPlug.hpub2_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.hpub2_H

/--
info: 'Spike.Lib.X64.HelloPh.RootPlug.RootRest.toBase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlug.RootRest.toBase
