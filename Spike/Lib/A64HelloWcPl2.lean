/-
**hello.w's `wc_main` own nodes placed** (AArch64; the `hpl` half; the hello twin of
wake's `WakePlacedCal` node lemmas at frame 144): `WcW2.wcWf_W2H`'s premise `hpl`, `WcMainWH` at
`PlacedSE Λ lbl · · []`, from the two placements at the slots (`SpawnPl.hpl_GJ1H`, `SpawnPl.hplQ_GJ1H`).

Every node of `WcMainWH` reads main's source's words at `wc_main`'s slots: the cell at `-104`, main's id at
`-112`, the slice's `x0`, `x2`, `x3` at `-144`, `-128`, `-120` (the fence and the reserve's call through `wcJH`,
past them through `WcSp6.FrWH`); no block of `wc_main` stores to those five slots (`keepsH_*`).

- `slots_absH`: the five slots read `σ`'s words at an abstract state's machine data.
- `PlH`: a node's states placed wherever the five slots read its abstract state's words.
- `nodeW_plH`, `blkW_plH`: a node and a block keeping the five slots inside `PlacedSE`.
- `KeepsH`, `keepsH_*`: `wc_main`'s blocks keep the five slots.
- `wcMainW_plH`: `WcMainWH` at `PlacedSE` from the two placements at the slots (`Hs`, `HsQ`).
- `wcMainW_plGJ1H`: the same at a ghost of `GJ1H` (`hpl`'s instance for `wcWf_W2H`).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloSpawnPl
import Spike.Lib.A64HelloWcW1

namespace Spike.Lib.A64.HelloPh.WcPl2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region Ctl)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.HelloWc (WcMainWH FrMGH rNH wcN3H aNH resBH tcb2CallH sp4AH initCallH)
open Spike.Lib.A64.HelloPh.WcSp6 (FrWH wcN6H wcN6fH wcN6aH sp6AH cloneArgsH oWH)
open Spike.Lib.A64.HelloPh.Ti2 (SlotPH SlotSlH)
open Spike.Lib.HelloHMid (SBH QBH slWsH)
open Spike.Lib.WakeSrcCtl (keepsSlot arun_slot_keep)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {Λ : Scc.Sem.Layout}
  {lbl : Lbl}

/-! ## The five slots -/

/-- **The five slots read `σ`'s words** at machine data `m` of `Abs R o m σ`, the region holding `-144 .. 0`. -/
theorem slots_absH (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {o : Spike.Lib.A64.Flow.SO} {m : MachineData}
    {σ : Spike.Lib.A64.Flow.AS} (hA : Spike.Lib.A64.Flow.Abs R o m σ) :
    SlotPH R (σ.slot (-104)).toNat (σ.slot (-112)).toNat m ∧
      SlotSlH R (σ.slot (-144)).toNat (σ.slot (-128)).toNat (σ.slot (-120)).toNat m := by
  obtain ⟨j104, e104, v104⟩ := hA.slot (-104) ⟨by decide, by omega, by omega⟩
  obtain ⟨j112, e112, v112⟩ := hA.slot (-112) ⟨by decide, by omega, by omega⟩
  obtain ⟨j144, e144, v144⟩ := hA.slot (-144) ⟨by decide, by omega, by omega⟩
  obtain ⟨j128, e128, v128⟩ := hA.slot (-128) ⟨by decide, by omega, by omega⟩
  obtain ⟨j120, e120, v120⟩ := hA.slot (-120) ⟨by decide, by omega, by omega⟩
  exact ⟨⟨j104, j112, e104, by rw [v104], e112, by rw [v112]⟩, ⟨j144, e144, by rw [v144]⟩,
    ⟨j128, e128, by rw [v128]⟩, ⟨j120, e120, by rw [v120]⟩⟩

/-- **A node's states placed at the slots**: every state of `n.J σ c` is placed (`lbl`) wherever the five slots
read `σ`'s words. -/
def PlH (Λ : Scc.Sem.Layout) (lbl : Lbl) (R : Region) (n : ND) : Prop :=
  ∀ σ c, n.J σ c → ∀ s : State, SlotPH R (σ.slot (-104)).toNat (σ.slot (-112)).toNat s.st.1 ∧
    SlotSlH R (σ.slot (-144)).toNat (σ.slot (-128)).toNat (σ.slot (-120)).toNat s.st.1 → PlacedSE Λ lbl s c []

/-- **A node placed at the slots is inside `PlacedSE`**, at no move. -/
theorem nodeW_plH (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {n : ND} (h : PlH Λ lbl R n) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨_, _, _, _, σ, hA, _, hj⟩ => ⟨h σ c hj s (slots_absH hlo hhi hA), fun _ h => h⟩

/-- **The block keeps the five slots** from the offsets `o`. -/
def KeepsH (o : Spike.Lib.A64.Flow.SO) (blk : List Directive) : Bool :=
  ([-104, -112, -144, -128, -120] : List Int).all fun j => keepsSlot j o blk

/-- **A block keeping the five slots, its node placed at them, is inside `PlacedSE`**, at no move
(`WakeSrcCtl.arun_slot_keep`). -/
theorem blkW_plH (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {n : ND} {blk : List Directive} (h : PlH Λ lbl R n)
    (hk : KeepsH n.o blk = true) : BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  have e : ∀ j ∈ ([-104, -112, -144, -128, -120] : List Int),
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot j =
        σ.slot j :=
    fun j hm => arun_slot_keep _ j blk ⟨n.pc, n.o, σ⟩ k (List.all_eq_true.mp hk j hm)
  have hs := slots_absH hlo hhi hA
  rw [e (-104) (by simp), e (-112) (by simp), e (-144) (by simp), e (-128) (by simp), e (-120) (by simp)] at hs
  exact ⟨h σ c hj _ hs, fun _ h => h⟩

/-! ## `wc_main`'s blocks keep the five slots -/

theorem keepsH_res : KeepsH ⟨-144, []⟩ resBH = true := by decide +kernel
theorem keepsH_tcb2 : KeepsH oWH tcb2CallH = true := by decide +kernel
theorem keepsH_sp4 : KeepsH oWH sp4AH = true := by decide +kernel
theorem keepsH_init : KeepsH oWH initCallH = true := by decide +kernel
theorem keepsH_sp6 : KeepsH oWH sp6AH = true := by decide +kernel
theorem keepsH_clone : KeepsH oWH cloneArgsH = true := by decide +kernel

/-! ## `wc_main`'s own nodes placed -/

section Main

variable {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {l : WeakMem.AllocLabel}
  {b : Nat} {ws : List TermRun.Word}

/-- **A node past the fence placed at the slots**: its states at the ghost's source `c0` and frame's words
(`FrWH`), placed wherever the slots read `b`, `me` and `sl` (`Hs`). -/
theorem plH_mid
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hM : MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me) {n : ND}
    (hJ : ∀ σ c, n.J σ c → c = c0 ∧ FrWH sl me cA fr σ) : PlH Λ lbl R n := by
  intro σ c hj s hs
  obtain ⟨rfl, h144, -, h128, h120, h112, h104, -, -⟩ := hJ σ c hj
  obtain ⟨_, _, ⟨-, hAb, -⟩, hcA⟩ := hM.1
  rw [h104, h112, h144, h128, h120, hcA, hAb] at hs
  exact Hs c sl me cA fr hM s hs

/-- **`WcMainWH` at `PlacedSE`** (`WcW2.wcWf_W2H`'s `hpl`): `wc_main`'s own nodes placed at `lbl`, from the
clone's source (`Hs`, at `SBH`) and the box's (`HsQ`, at `QBH`) placed wherever the slots read the cell `b`,
main's word `me` and the slice `sl` (`SpawnPl.hpl_GJ1H`, `SpawnPl.hplQ_GJ1H`). -/
theorem wcMainW_plH (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 [])
    (HsQ : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE Λ lbl s c0 []) :
    WcMainWH (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F F₂ ms J1 (SBH l b ws)
      (QBH l b ws) := by
  refine ⟨nodeW_plH hlo hhi ?_, blkW_plH hlo hhi ?_ keepsH_res, fun c0 sl me cA fr hM => ?_,
    fun c0 sl me cA fr hM => ⟨?_, ?_, ?_⟩, fun c0 sl me cA fr hM => ⟨?_, ?_, ?_⟩⟩
  -- the fence
  · rintro σ c ⟨l', A, ⟨q, ⟨σe, hJ1, -, -, h144, -, h128, h120, h112⟩, hA, -⟩, hQ⟩ s hs
    rw [hA, hQ.2.1, h112, h144, h128, h120] at hs
    exact HsQ c _ _ (σ.slot (-104)) (σe.regs.X29.toBitVec, σe.regs.X30.toBitVec)
      ⟨⟨l', A, hQ, hA⟩, σe, q.1.c0, hJ1, rfl, rfl, rfl⟩ s hs
  -- the reserve's call
  · rintro σ c ⟨l', A, hS, q, ⟨σe, hJ1, -, -, h144, -, h128, h120, h112⟩, hA⟩ s hs
    rw [hA, hS.2.1, h112, h144, h128, h120] at hs
    exact Hs c _ _ (σ.slot (-104)) (σe.regs.X29.toBitVec, σe.regs.X30.toBitVec)
      ⟨⟨l', A, hS, hA⟩, σe, q.1.c0, hJ1, rfl, rfl, rfl⟩ s hs
  -- `.sp3`
  · exact blkW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2⟩) keepsH_tcb2
  -- `.sp4`'s block, the tid store, `scc_rt_thread_init`'s call block
  · exact blkW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2.1⟩) keepsH_sp4
  · exact nodeW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2.2.2.1⟩)
  · exact blkW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2⟩) keepsH_init
  -- `.sp6`'s block, the fence before the clone, the clone's arguments
  · exact blkW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2.2⟩) keepsH_sp6
  · exact nodeW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2.2.2⟩)
  · exact blkW_plH hlo hhi (plH_mid Hs hM fun _ _ h => ⟨h.1, h.2.2.2.2⟩) keepsH_clone

end Main

/-- **`WcW2.wcWf_W2H`'s `hpl` at a ghost of `GJ1H`** (rodata's label `lr`, the box's `l'` fresh at `lbl1`, main's
id at the TCB): `wc_main`'s own nodes placed at the twice extended placement `upd lbl1 l' b'`
(`wcMainW_plH` at `SpawnPl.hpl_GJ1H`, `SpawnPl.hplQ_GJ1H`). -/
theorem wcMainW_plGJ1H {L : RuntimeLayout} {ms : Spike.Lib.MemSide isaLSE2}
    {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    {F' : MachineData → Prop} {t : UInt64} (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hl' : lbl1 l' = none) (hmt : lbl1 (Spike.Lib.WakeT1.mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.HelloH2G.GJ1H L lbl1 lr R F' J1 t) :
    WcMainWH (fun s c => PlacedSE L.Λ (Spike.Lib.A64ConsumerA.upd lbl1 l' b') s c []) (fun _ _ => False) exe endPc
      R F F₂ ms J1 (SBH l' b' (slWsH lr)) (QBH l' b' (slWsH lr)) :=
  wcMainW_plH hlo hhi (SpawnPl.hpl_GJ1H hl' hmt hG) (SpawnPl.hplQ_GJ1H hl' hmt hG)

end Spike.Lib.A64.HelloPh.WcPl2

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.WcPl2.slots_absH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl2.slots_absH

/-- info: 'Spike.Lib.A64.HelloPh.WcPl2.blkW_plH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl2.blkW_plH

/-- info: 'Spike.Lib.A64.HelloPh.WcPl2.wcMainW_plH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl2.wcMainW_plH

/-- info: 'Spike.Lib.A64.HelloPh.WcPl2.wcMainW_plGJ1H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl2.wcMainW_plGJ1H
