/-
**The start segment inside `WSX` at the root's context, the child's stack
carried unmapped** (wake.w, x86-64): `StartPlace.wake_start_wc_placeXT` at
wake's arena `arW`, the clone phase `ClW`, the start control `c0W`, the
level `WSX` at the root's context `Land.CtxR (Ly) c0W (Land.refW …)`, with
the thread init (`RootTi.hti_root`), `hWp`/`hWs` (`WcWfR.hWp_R`/`hWs_R`) and
the box premises (as `StartH0.wake_start_wc_h0`) discharged, and `hxa`
from `h1`'s `Box` clause (`Hxa.box_landing`) with the child's stack
`r1Of` unmapped taken from the segment itself (`KeepUn.SegW.keepUn`): the
open `hUn1` of `Hxa.hxa_R` does not arise.

The segment runs at `msU`: the memory side `MS` (`msOfA` at `ownGXW`,
`arW`, `I2 arW L0T ls0T inv0 inv1`) with every allocation landing asked
only with `r1Of` unmapped (`invU`); `SegW.mono_xa` moves it to
`KeepUn.unXa MS r1Of`, `keepUn` (the take of `rS0`, disjoint from `r1Of`,
keeps it unmapped) back to `MS`, with `U r1Of` at its entry and its exit.
The entry's `U r1Of` holds at the loaded thread (`entry_U`).

- `SegW.mono_xa`: a segment under a memory side with a larger allocation
  fragment.
- `wcPreW_xa`, `wcSp0W_xa`: `WcPreW` / `WcSp0W` read no `xa`.
- `unowned_stack`: a range in the stack pool is off the entry stack's
  private memory (`WakeOHinit.unowned_stack`'s twin).
- `entry_U`: the loaded thread has `r1Of` unmapped and is `WideSt`.
- `invU`, `msU`: `MS`'s fragment asked only with `r1Of` unmapped.
- `wake_start_wc_h0X`: the statement.

x86-64 twin of `Spike/Lib/A64WakeStartH0U.lean` (namespace
`Spike.Lib.X64.WakePh.StartH0X`).

**Where x86-64 differs from AArch64**:
- the level is `WSX` (main owns its and the worker's TCB words, `ownGXW`),
  so the segment is `wake_start_wc_placeXT`'s (A64 `StartH0G.wake_start_wc_h0W`
  at `WS`/`ownG`), with its premises discharged here rather than in a
  separate `StartH0G` module: the thread init by `RootTi.hti_root` (the
  arena offsets copied from `WcWfR.offW_own`), `hWp`/`hWs` by
  `WcWfR.hWp_R`/`hWs_R` at `refW` transported to `msU` (`wcPreW_xa`,
  `wcSp0W_xa`; A64 leaves them premises), the box premises as
  `StartH0.wake_start_wc_h0`'s proof at `own := ownGXW`;
- the memory side is generic in `I2`'s `inv0`/`inv1` and the landing's
  frame `F0`, `h1`'s `Box ⊆ inv1` clause taken as `hB1` (A64 at
  `msBot E []` with the whole `WakeRoot.H1R`);
- the entry is stated, not the root's `hst0` (x86-64 has no `StartH0B`
  twin on this branch): the pre carries `FWN ∧ Pz rS0` and `U r1Of`
  (`entry_U` and `RootP.pz_rS0_load` give the latter two at the loaded
  thread);
- `c0W`'s placement (`hpl0`) and code facts (`hC0`) stay premises (A64
  `WakeImmsC0.placedSE_c0WW`, `WakeC0CF.cfacts_c0WW`; no x86-64 producer);
- the arena's units and offset are proved here (`units_off`, as
  `StartH0`'s private one).
-/
import Spike.Lib.X64WakeHxa
import Spike.Lib.X64KeepUn
import Spike.Lib.X64WakeWcTopS
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeRootP
import Spike.Lib.DmemPriv

namespace Spike.Lib.X64.WakePh.StartH0X

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize Unowned)
open Spike.Lib.X64ConsumerA (msOfA I2)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W AGB bX wX)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib (Arena Frag FragS MemSide Region SegW PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64.WakeC0 (c0W)

/-- **A segment under a memory side with a larger allocation fragment**
(`Out.mono_xa` at every state of the invariant). -/
theorem SegW.mono_xa {W : Frag isa} {K : State → State → Prop} {p : Prog} {lbl : Lbl}
    {ms ms' : MemSide isa} {P Q : Frag isa} (h : SegW W K p lbl ms P Q)
    (he : ms' = { ms with xa := ms'.xa }) (hxa : ∀ l b n s c, ms.xa l b n s c → ms'.xa l b n s c) :
    SegW W K p lbl ms' P Q := by
  obtain ⟨inv, hP, hW, hcl⟩ := h
  exact ⟨inv, hP, hW, fun s c hi =>
    ⟨fun hk => Spike.Lib.X64ConsumerA.Out.mono_xa ((hcl s c hi).1 hk) he hxa, (hcl s c hi).2⟩⟩

/-- **`WcPreW` reads no `xa`.** -/
theorem wcPreW_xa {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {X : WeakMem.AllocLabel → Nat → Nat → Frag isa}
    {J0 Jc : Spike.Lib.X64.AS → Ctl → Prop}
    (h : WcPreW W K exe endPc R F ms J0 Jc) : WcPreW W K exe endPc R F { ms with xa := X } J0 Jc :=
  { pro := { h.pro with }, e := h.e,
    alloc := fun q hq hra => { h.alloc q { hq with toS := { hq.toS with } } hra with } }

/-- **`WcSp0W` reads no `xa`.** -/
theorem wcSp0W_xa {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {X : WeakMem.AllocLabel → Nat → Nat → Frag isa}
    {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    (h : WcSp0W W K exe endPc R F ms J0) : WcSp0W W K exe endPc R F { ms with xa := X } J0 :=
  ⟨fun s σ c he hn hd hpc hA hF hJ => h.b s σ c he hn hd hpc hA hF (by
      obtain ⟨q, h1, h2, h3⟩ := hJ
      exact ⟨⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, h1, h2, h3⟩),
   fun s c hA => h.st s c (by
      obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, q, o, h1⟩ := hA
      exact ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, o, h1⟩)⟩

/-- The arena's units of a type with accesses are positive, its offset one
header word (as `StartH0`'s private `units_off`). -/
private theorem units_off {Λ : Scc.Sem.Layout} {τ : Ty}
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us) :
    1 ≤ (Spike.Lib.X64.Rt.arOf Λ).units 1 τ ∧ (Spike.Lib.X64.Rt.arOf Λ).off 1 τ = 8 := by
  obtain ⟨us, hus⟩ := hacc
  refine ⟨?_, ?_⟩
  · simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus]
    split <;> omega
  · simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus, Nat.mul_zero]

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "KW" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "μE" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
local notation "GW" => Spike.Lib.X64WakeOG.gW hpw i (Spike.Lib.X64WakeHG.cTW hpw i)

set_option hygiene false in
local notation "OWN" => fun s (_ : List TermRun.Frame) => Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab) s

set_option hygiene false in
/-- The memory side: `refW`'s, with `I2`'s fragment. -/
local notation "MS" => msOfA (Ly).Λ (μE) (fun _ => True) (GW) (OWN) (AR)
  (I2 (AR) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1) (L0T (Ly).Λ) (ls0T (ls0 E)) []

set_option hygiene false in
/-- The root's context at `c0W`. -/
local notation "CX" => Spike.Lib.X64.WakePh.Land.CtxR (Ly) c0W (Spike.Lib.X64.WakePh.Land.refW asm hpw i ls0 E)

set_option hygiene false in
/-- The start's level at `ownGXW` at the root's context. -/
local notation "WSR" => Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (AR) wakeSrc Dt (Spike.Lib.X64.WakeOD.ClW hpw i)
  (CX) (L0T (Ly).Λ) (ls0T (ls0 E)) frM (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

/-- **A range in the stack pool is off the entry stack's private memory.** -/
theorem unowned_stack {E : Entry} (hE : E.clear (Ly).Λ = true) {r : Range} (hr : r.Sub (Ly).Λ.stackPool)
    (hw : r.lo + r.size ≤ 2 ^ 64) (s : State) (hs : s.st.1.dmem = E.stackMem) : Unowned r s := by
  intro a ha hm
  rw [hs, Spike.Lib.DmemPriv.mem_stackMem (Entry.clear_disjoint hE).1] at hm
  have hd := (Entry.clear_disjoint hE).2 _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.stackPool ∈ (Ly).Λ.regions)
  have ha' : (BitVec.ofNat 64 a).toNat = a := by
    simp only [Range.contains] at ha; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [ha'] at hm
  obtain ⟨h1, h2⟩ := hr
  simp only [Range.contains, Range.Disjoint] at ha hm hd
  omega

/-- **The loaded thread has the child's stack unmapped** (and is `WideSt`,
`wideSt_threadAt`). -/
theorem entry_U {E : Entry} (hE : E.clear (Ly).Λ = true)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (base : Nat) (syms : List (String × Nat)) :
    U R1 (Scc.Sem.X64.threadAt E base o.prog syms) := by
  obtain ⟨-, hs1, -, -, -, -, hw1⟩ :=
    Spike.Lib.X64WakeOSide.ranges_W hpw i (Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hpw i hA13)
  exact ⟨Scc.Cert.WideX64.wideSt_threadAt (Spike.Lib.PlaceWX.wideIn_of_placeWX hpw) E base syms,
    unowned_stack hpw i hE hs1 hw1 _ rfl⟩

/-- **`MS`'s fragment asked only with the child's stack unmapped.** -/
abbrev invU (inv0 : FragS isa) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (E : Entry) :
    Spike.Lib.X64ConsumerS.InvS := fun lbl lsize s c fs =>
  U R1 s → I2 (AR) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1 lbl lsize s c fs

/-- **`MS` at `invU`.** -/
noncomputable abbrev msU (inv0 : FragS isa) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (E : Entry) :
    MemSide isa :=
  msOfA (Ly).Λ (μE) (fun _ => True) (GW) (OWN) (AR) (invU hpw i ls0 inv0 inv1 E) (L0T (Ly).Λ) (ls0T (ls0 E)) []

set_option hygiene false in
local notation "MU" => msU asm hpw i ls0 inv0 inv1 E

set_option maxHeartbeats 3200000 in
/-- **From `_start` to `wc_main`'s heap abort inside `WSX` at the root's
context, the child's stack carried unmapped**: `wake_start_wc_placeXT` at
`msU` (`hti` by `RootTi.hti_root`, `hWp`/`hWs` by `WcWfR.hWp_R`/`hWs_R`,
the box premises as `StartH0.wake_start_wc_h0`), `hxa` by
`Hxa.box_landing` and `h1`'s `Box` clause `hB1` given `U r1Of`, which
`SegW.mono_xa` and `KeepUn.SegW.keepUn` carry from the entry. -/
theorem wake_start_wc_h0X {E : Entry} (hE : E.Ok (Ly).Λ)
    {Dt : State → Prop} {frM : TermRun.Frame} {ax : Int64} {lbl' : Lbl}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {F0 : MachineData → Prop}
    (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    /- `c0W`'s placement and code facts (no x86-64 producer) -/
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hC0 : Spike.Lib.X64Consumer.CFacts (Ly).Λ lbl' c0W)
    /- `h1`'s `Box ⊆ inv1` clause and `wc_main`'s frame inside `F0` -/
    (hB1 : ∀ l b n, L0T (Ly).Λ l = none → Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n →
      ∀ s c, Spike.Lib.X64.Flow.WakeWc.Box (Ly) (MS) F0 l b n s c → inv1 l b n s c [])
    (hF0 : ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC m → F0 m) :
    SegW (WSR) (KW) wakeSrc (L0T (Ly).Λ) (MS)
      (fun s c => At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ Spike.Lib.X64Consumer.Pz (RS0) m)
        (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0W) s c ∧ U R1 s)
      (fun s c => (∃ v m0 σC,
        At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
          (wX (MS) (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) .abort) s c ∧ TP (TV) s) ∧ U R1 s) := by
  have hL := Spike.Lib.PlaceWX.link i hpw
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  -- the ranges: `r1Of` in the pool, disjoint from `rS0`, both in the address space
  have hsub1 := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hpw i hA13
  obtain ⟨-, -, -, -, hd0, hwS0, hw1⟩ := Spike.Lib.X64WakeOSide.ranges_W hpw i hsub1
  have hr0 : Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab = RS0 := Spike.Lib.X64.WakePh.RootP.r0Of_rS0
  have hd : (R1).Disjoint (RS0) := by
    have := hd0; simp only [Spike.Lib.X64WakeOSide.r1W, Spike.Lib.X64WakeOSide.r0W, hr0] at this; exact this
  have hwS : (RS0).lo + (RS0).size ≤ 2 ^ 64 := by
    have := hwS0; simp only [Spike.Lib.X64WakeOSide.r0W, hr0] at this; exact this
  -- the arena's facts (as `StartH0.wake_start_wc_h0`)
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hL
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MU).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MU).cells = 4194304 := rfl
  have hct : (MU).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hacc1 : ∃ us, TermRun.accs (TermRun.close [] .int) = some us := ⟨_, rfl⟩
  obtain ⟨hu1, hf1⟩ := units_off (Λ := (Ly).Λ) hacc1
  have hf1' : (MU).off 1 .int = 8 := hf1
  have hu2 : (MU).units 1 .int = 2 := rfl
  have hctrB : ∀ k < 8, (Ly).Λ.data.contains ((BitVec.ofNat 64 (MU).ctr).toNat + k) := fun k hk => by
    rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold Scc.Sem.Range.contains; omega
  have hG : ∀ a : BitVec 64, a.toNat < 2 ^ 32 → ((Ly).Λ.heap.contains a.toNat ∨ (Ly).Λ.data.contains a.toNat) →
      ∀ v, (MU).G ⟨a, 8⟩ v := fun a ha hm v => by
    have := Spike.Lib.X64WakeOG.hGpl_ofPlaceW2 hpw i hpin2 a.toNat v hm
    refine .inr ?_
    simpa [Scc.Sem.wordLoc] using this
  have hoff : ∀ q : Call, q.OKB (MU) (Ly).lab → (MU).off q.n q.τ ≤ 16 * (MU).units q.n q.τ := fun q hq => by
    obtain ⟨hu, hf⟩ := units_off (Λ := (Ly).Λ) hq.toS.accs
    have hu' : 1 ≤ (MU).units 1 q.τ := hu
    have hf' : (MU).off 1 q.τ = 8 := hf
    rw [hq.one, hf']; omega
  have hrt0 := Spike.Lib.X64.WakePh.StartH0.rt_L0T (Λ := (Ly).Λ) hstat (ls0 E)
  obtain ⟨e, he⟩ := Spike.Lib.X64.WakeC0.c0W_box.term
  obtain ⟨w, hw, hw0⟩ := Spike.Lib.X64.WakeC0.c0W_box.ev
  have hbq : ∀ q : AGB (MU) (Ly).lab, q.1.c0 = c0W → q.1.a = .var "z" ∧ q.1.τ = .int ∧ q.1.ws = [w] := by
    intro q hq
    obtain ⟨_, ht⟩ := q.2.term; rw [hq, he] at ht
    obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
    have ha' := (Op.new.inj ha).1
    have hev := q.2.ev; rw [hq, ← ha', hw] at hev
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hev)
    exact ⟨ha'.symm, h1.symm, h2.symm⟩
  have hq0 : ∃ q : Call, q.OKB (MU) (Ly).lab ∧ q.c0 = c0W ∧ q.h = 256#64 ∧ q.k = 1#64 ∧ q.u (MU) = 2#64 := by
    refine ⟨⟨c0W, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩,
      ⟨⟨.inr ⟨trivial, .var "z", [w], ⟨_, he⟩, hw, rfl⟩, Spike.Lib.X64.WakeC0.c0W_box.hold,
        by show (1 : Nat) < 2 ^ 64; decide,
        Spike.Lib.X64.Rt.ArenaW.arOf_ctrLab hL .linux, Spike.Lib.X64.Rt.ArenaW.arOf_heapLab hL .linux,
        by rw [hh]; omega, rfl, by rw [hu2]; decide, by rw [hf1']; simp [Spike.Lib.X64.Alloc.mOf], hacc1, hrt0 _,
        Spike.Lib.X64.WakePh.StartH0.mp_dataW hpw i hctrB,
        fun _ _ _ => hG _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
          (.inr (by rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨hc1, by omega⟩)) _,
        fun o' _ ho => ?_⟩, trivial, ⟨_, he⟩, hw, rfl⟩, rfl, rfl, rfl, rfl⟩
    have hd : Call.hdrAt (MU) ⟨c0W, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩ o' =
        (Ly).Λ.heap.lo + 16 * o' := by simp [Call.hdrAt, hh, Spike.Lib.X64.Alloc.mOf]
    rw [hu2, hcl] at ho
    have hT : (BitVec.ofNat 64 (Call.hdrAt (MU) ⟨c0W, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩ o')).toNat
        = (Ly).Λ.heap.lo + 16 * o' := by rw [hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨hrt0 _, Spike.Lib.X64.WakePh.StartH0.mp_heapW hpw i fun k hk => ?_, hG _ (by omega) (.inl ?_) _⟩
    · rw [hT]; unfold Scc.Sem.Range.contains; omega
    · rw [hT]; unfold Scc.Sem.Range.contains; omega
  -- the runtime's words off the arena (as `WcWfR.offW_own`)
  have hrt : ∀ w ∈ (Ly).rtWords, ¬ ((AR).heap ≤ w.toNat ∧ w.toNat < (AR).heap + 16 * (AR).cells) ∧
      (⟨w, 8⟩ : Loc) ≠ (AR).ctrLoc := fun w hw => by
    have hm := ((Ly).words_mapped w hw).2.2 0 (by decide)
    obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (show (Ly).Λ.WF from hwf).disjoint
    have hsep : Scc.Cert.Rt.X64.WordSep w (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
      Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hpw) w hw
    have hh' : (AR).heap = (Ly).Λ.heap.lo := rfl
    have hc' : (AR).cells = Scc.Cert.PlaceOK.allocCells := rfl
    have hu' : (AR).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint, Scc.Cert.Rt.X64.WordSep] at hm hdh hph hsep
    refine ⟨by rw [hh', hc']; omega, fun he => ?_⟩
    simp only [Arena.ctrLoc, Loc.mk.injEq, and_true] at he
    rw [hu'] at he; subst he
    omega
  -- the thread init (`RootTi.hti_root` at `F := FWN`, `P := Pz rS0`)
  have hti := Spike.Lib.X64.WakePh.RootTi.hti_root (L := Ly) (F := FWN) (ar := AR) (p := wakeSrc) (Dt := Dt)
    (Cl := Spike.Lib.X64.WakeOD.ClW hpw i) (Ctx := CX) (lbl := L0T (Ly).Λ) (lsize := ls0T (ls0 E)) (frM := frM)
    hpo hlo (fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hpo]; exact h))
    (Spike.Lib.PlaceWX.site_ofPlaceWX hpw i) (fun _ h => h.2) Spike.Lib.X64.WakeC0.c0W_ctl hpl0 hax hE
    (Spike.Lib.PlaceWX.abortLbl_of_placeWX hL) (Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw i hA13)
    (Spike.Lib.X64WakeOSide.hro_W hpw i) hC0 (fun _ h => h.2) hrt
  -- `hWp`/`hWs` at `refW`, moved to `msU`
  have hWp := fun v m0 σC => wcPreW_xa (X := (tpXa (MU) (TV)).xa)
    (Spike.Lib.X64.WakePh.WcWfR.hWp_R asm hpw i c0W ls0 hpo hlo hc hA13 (Dt := Dt)
      (Cl := Spike.Lib.X64.WakeOD.ClW hpw i) (frM := frM) (fun _ h => h.2) hax Spike.Lib.X64.WakeC0.c0W_ctl hpl0 E v m0 σC)
  have hWs := fun v m0 σC => wcSp0W_xa (X := (tpXa (MU) (TV)).xa)
    (Spike.Lib.X64.WakePh.WcWfR.hWs_R asm hpw i c0W ls0 hpo hlo hc hA13 Spike.Lib.X64.WakeC0.c0W_box
      (Dt := Dt) (Cl := Spike.Lib.X64.WakeOD.ClW hpw i) (frM := frM) (fun _ h => h.2) hax
      Spike.Lib.X64.WakeC0.c0W_ctl hpl0 E v m0 σC)
  -- `hxa` at `msU`: the landing is a `Box` given `U r1Of`
  have hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC)
        (bX (MU) (Ly).lab ((JW) σC) l A) s c → TP (TV) s → (MU).xa l A 1 s c := by
    intro v m0 σC l A s c hl hA htp
    have hA' : At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8))
        (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (bX (MS) (Ly).lab ((JW) σC) l A) s c := by
      obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, q, hq⟩ := hA
      exact ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hq⟩
    obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := hA
    obtain ⟨hu, hf⟩ := units_off (Λ := (Ly).Λ) q.2.toS.accs
    have hu' : 1 ≤ (MU).units 1 q.1.τ := hu
    have hf' : (MU).off 1 q.1.τ = 8 := hf
    have hAL : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells A 1 := by
      show (MU).heap + 8 ≤ A ∧ A + 8 * 1 ≤ (MU).heap + 16 * (MU).cells ∧ 1 + 1 ≤ (MU).cells
      rw [hf'] at hAo; omega
    exact ⟨hAL, fun hU => .inr ⟨l, A, 1, hl, hAL, rfl, rfl, hB1 l A 1 hl hAL s c
      (Spike.Lib.X64.WakePh.Hxa.box_landing hpw i hA13 hF0 hA' htp hU)⟩⟩
  -- the start segment at `msU`, then at `unXa MS r1Of`, then `keepUn`
  have hG0 := Spike.Lib.X64.WakePh.StartPlace.wake_start_wc_placeXT hpw i hE (ar := AR) (p := wakeSrc) (Dt := Dt)
    (Cl := Spike.Lib.X64.WakeOD.ClW hpw i) (Ctx := CX) (lbl := L0T (Ly).Λ) (lsize := ls0T (ls0 E)) (frM := frM)
    (ar' := AR) (I := invU hpw i ls0 inv0 inv1 E) (L0 := L0T (Ly).Λ) (ls0 := ls0T (ls0 E)) (pS := wakeSrc)
    (lblS := L0T (Ly).Λ) (P := Spike.Lib.X64Consumer.Pz (RS0))
    hpo hlo (fun _ h => h.2) Spike.Lib.X64.WakeC0.c0W_ctl hpl0 hax
    (Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw i hA13) hA13 (Spike.Lib.X64WakeOSide.hro_W hpw i) hC0
    (Spike.Lib.X64.WakePh.StartPlaceLy.hfree_W hpw i hstat (ls0 E))
    (Spike.Lib.X64.WakePh.StartPlaceLy.hctr2_of_data hpw i hpin2 hctrD)
    (Spike.Lib.X64.WakePh.StartPlaceLy.hcT_W hpw i) ⟨rfl, rfl, rfl⟩
    (Spike.Lib.X64.WakePh.RootP.pz_rS0_fstable hE) hti hq0 (Nat.le_refl _) (by rw [hh, hcl, ← hA]; omega)
    (by rw [hh, hcl]; omega) (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩)
    hoff (fun q hq => by rw [(hbq q hq).2.1, hf1', hu2]; omega)
    (fun q _ => Spike.Lib.X64.WakePh.StartH0.mp_cellW hpw i q)
    (fun q hq => ⟨w, (hbq q hq).2.2, by rw [(hbq q hq).2.1]; rfl, by rw [hw0]; exact ⟨by decide, rfl⟩⟩)
    hWp hWs hxa
  have hG1 := SegW.mono_xa (ms' := unXa (MS) (R1)) hG0 rfl fun _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩
  have hG := Spike.Lib.X64.KeepUn.SegW.keepUn rfl hG1 fun _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hs
  refine hG.mono_post fun s c hQ => ?_
  obtain ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hD, h0, h30, q, hq, hJ⟩, htp⟩, hu⟩ := hQ
  exact ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hD, h0, h30, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hq, hJ⟩,
    htp⟩, hu⟩

end Spike.Lib.X64.WakePh.StartH0X

/-- info: 'Spike.Lib.X64.WakePh.StartH0X.SegW.mono_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0X.SegW.mono_xa

/-- info: 'Spike.Lib.X64.WakePh.StartH0X.wcPreW_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0X.wcPreW_xa

/-- info: 'Spike.Lib.X64.WakePh.StartH0X.wcSp0W_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0X.wcSp0W_xa

/-- info: 'Spike.Lib.X64.WakePh.StartH0X.unowned_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0X.unowned_stack

/-- info: 'Spike.Lib.X64.WakePh.StartH0X.entry_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0X.entry_U

/-- info: 'Spike.Lib.X64.WakePh.StartH0X.wake_start_wc_h0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0X.wake_start_wc_h0X
