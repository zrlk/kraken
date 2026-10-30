/-
**`wc_main`'s obligations past the box's store at `h1`'s outside move**
(AArch64, the pre-spawn consumer; `WakeH1Inv.K1W`'s, `X1W`'s pc guards):
from `WcMidW` at a stack take at `a` (`wcMidW_wcG`'s `PhRec.K L rK`) to
`WcMidW` at the take of the site's range or a `clone` refusal
(`TakeCKS a Cl`, `Cl` only at the clone's pc), the states off the clone's
and the take's pcs (what `WakeH1Inv.x1W_off` asks).

- `nodeW_mapWK`, `blkW_mapWK`, `reserveW_mapWK`, `tcbWG_mapWK`,
  `WcResW.mapWK`, `WcSp3W.mapWK`, `WcSp4W.mapWK`, `WcMidW.mapWK`: node
  obligations under a pointwise change of the predicate and the outside move.
- `takeK_pc`, `takeCKS_none`: a state no take at `a` moves is off `a`; off
  `a` and the clone's pc, no take of the site's range and no refusal moves it.
- `ckRuns`, `ckIn`, `ck_chk`, `ck_ne`: the pcs of `WcMidW`'s nodes (`wc_main`
  from `.sp0 + 16` to the `svc`, `scc_rt_thread_reserve`,
  `scc_rt_alloc_tcb`, `scc_rt_thread_init`'s entry), none the clone's
  (`cloneAt pfxM exe`, `.sp6 + 52`) nor the take site's
  (`scc_rt_take_site`), decided on the listing.
- `OffC`, `nodeW_offC`, `nodeW_offC0`, `blkW_offC`, `blkW_offC0`,
  `wcMidW_offC`: `WcMidW`'s states off the clone's pc and the take site's.
- `wcMidW_k1`: `WcMidW` at `TakeCKS a Cl` with both pcs avoided, from
  `WcMidW` at `TakeK a rK`.
- `wcMidW_k1S`: the same at the take site's label, from the listing alone.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeWcMidW
import Spike.Lib.A64RunsOff

namespace Spike.Lib.A64.Flow.WakeWc

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Flow (ND BlkW NodeW At AS)
open Spike.Lib.A64.Rt (TcbGG TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.A64ConsumerA (TakeKS TakeCKS)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.WakePreA (cloneAt)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays)
open Scc.Sem.A64 (pcOf)

/-! ## A pointwise change of the predicate and the outside move -/

section Map

variable {W W' : Frag isaLSE2} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}
  (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s')
include hf

/-- A node's obligation under a pointwise change. -/
theorem nodeW_mapWK {n : ND} (h : NodeW W K exe endPc R F n) : NodeW W' K' exe endPc R F n :=
  fun s c hs => hf s c (h s c hs).1 (h s c hs).2

/-- A block node's obligation under a pointwise change. -/
theorem blkW_mapWK {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk) :
    BlkW W' K' exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    hf _ c (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).2

/-- The reserve's node obligations under a pointwise change. -/
theorem reserveW_mapWK {q : ResG} {i : Spike.Lib.A64.Rt.Reserve.RN} (h : ReserveW W K exe endPc R F q i) :
    ReserveW W' K' exe endPc R F q i := by
  cases i <;> dsimp only [ReserveW] at h ⊢ <;> first | exact blkW_mapWK hf h | exact nodeW_mapWK hf h

/-- `scc_rt_alloc_tcb`'s node obligations under a pointwise change. -/
theorem tcbWG_mapWK {q : TcbGG} {i : Ret0.TN} (h : TcbWG W K exe endPc R F q i) :
    TcbWG W' K' exe endPc R F q i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;> first | exact blkW_mapWK hf h | exact nodeW_mapWK hf h

/-- **From the fence to `.sp3`** under a pointwise change. -/
theorem WcResW.mapWK {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResW W K exe endPc R F ms J0 S Q) : WcResW W' K' exe endPc R F ms J0 S Q :=
  ⟨nodeW_mapWK hf h.f, blkW_mapWK hf h.bl, fun g hg i => reserveW_mapWK hf (h.res g hg i)⟩

/-- **From `.sp3` to `.sp4`** under a pointwise change. -/
theorem WcSp3W.mapWK {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp3W W K exe endPc R F c0 cA m fr) : WcSp3W W' K' exe endPc R F c0 cA m fr :=
  ⟨blkW_mapWK hf h.blk, fun g hg i => tcbWG_mapWK hf (h.tcb g hg i)⟩

/-- **From `.sp4` to the `svc`** under a pointwise change. -/
theorem WcSp4W.mapWK {F₂ : MachineData → Prop} {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp4W W K exe endPc R F F₂ c0 t cA m fr) : WcSp4W W' K' exe endPc R F F₂ c0 t cA m fr :=
  ⟨blkW_mapWK hf h.n4, nodeW_mapWK hf h.n4s, blkW_mapWK hf h.n5, nodeW_mapWK hf h.nI,
    blkW_mapWK hf h.n6, nodeW_mapWK hf h.n6f, blkW_mapWK hf h.n6a⟩

/-- **From the box's store to the `svc`** under a pointwise change of the
predicate and the outside move. -/
theorem WcMidW.mapWK {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidW W K exe endPc R F F₂ ms J0 S Q) :
    WcMidW W' K' exe endPc R F F₂ ms J0 S Q :=
  ⟨WcResW.mapWK hf h.res, fun c0 cA m fr hM => WcSp3W.mapWK hf (h.sp3 c0 cA m fr hM),
    fun c0 cA m fr hM => WcSp4W.mapWK hf (h.sp4 c0 cA m fr hM)⟩

end Map

/-! ## The outside moves at a state -/

/-- **A state no take at `a` moves is off `a`**: at `a` the take of any
range from its own memory moves it. -/
theorem takeK_pc {a : Int64} {rS : Scc.Sem.Range} {s : State} (h : ∀ s', ¬ TakeK a rS s s') : s.st.2 ≠ a :=
  fun he => h _ ⟨he, Scc.Sem.A64.abi.dmem s, rfl⟩

/-- **Off the take's pc `a` and the clone's pc `cpc`**, neither the take of
the site's range nor a refusal at `Cl` (only at `cpc`) moves a state. -/
theorem takeCKS_none {a : Int64} {Cl : State → Prop} {cpc : Nat} (hCl : ∀ s, Cl s → pcOf s = cpc) {s : State}
    (ha : s.st.2 ≠ a) (hc : pcOf s ≠ cpc) : ∀ s', ¬ TakeCKS a Cl s s' :=
  fun _ h => h.elim (fun h => ha h.1) fun h => hc (hCl s h.1)

/-- A pc off `a` as an `Int64` is off it as a number. -/
theorem pcOf_ne {a : Int64} {s : State} (h : s.st.2 ≠ a) : pcOf s ≠ a.toBitVec.toNat :=
  fun e => h (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq e))

/-! ## The nodes' pcs off the clone's -/

/-- **The runs of `WcMidW`'s nodes**: `wc_main` from `.sp0 + 16` to the
last instruction before the `svc`, `scc_rt_thread_reserve`,
`scc_rt_alloc_tcb` and `scc_rt_thread_init`'s entry. -/
def ckRuns : List (Label × Nat × Nat) :=
  [(".L21_wc_main.sp0", 4, 6), (".L21_wc_main.sp3", 0, 5), (".L21_wc_main.sp4", 0, 6),
   ("scc_rt_thread_init", 0, 1), (".L21_wc_main.sp6", 0, 13),
   (Flow.Reserve.fnL, 0, 4), (Flow.Reserve.entryL, 0, 16), (Flow.Reserve.okL, 0, 5),
   (Ret0.AllocTcb.fnL, 0, 6), (Ret0.AllocTcb.entryL, 0, 5), (Ret0.AllocTcb.lenL, 0, 48),
   (Ret0.AllocTcb.okL, 0, 43)]

/-- **The runs' pcs are neither the clone's** (`.sp6 + 4·13`) **nor the take
site's** (`scc_rt_take_site`), on the listing. -/
theorem ck_chk : Spike.Lib.A64.RunsOff.runsNeChk wakeProg ckRuns
    [(pfxM ++ ".sp6", 13), (Ret0.StackTake.siteL, 0)] = true := by
  decide +kernel

/-- **`n` instructions from `l + 4k` lie in one of the runs.** -/
def ckIn (l : Label) (k n : Nat) : Bool :=
  ckRuns.any fun r => r.1 == l && decide (r.2.1 ≤ k) && decide (k + n ≤ r.2.2)

section Off

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
  {endPc : Int64} {R : Region} {F : MachineData → Prop}
include hp

/-- **A pc of the runs is neither the clone's nor the take site's.** -/
theorem ck_ne {l : Label} {k n : Nat} (h : ckIn l k n = true) {j : Nat} (hj : j < n) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + j)) ≠ cloneAt pfxM exe ∧
      (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + j)) ≠
        (_root_.Executable.labels exe).label Ret0.StackTake.siteL := by
  obtain ⟨⟨l', lo, hi⟩, hr, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
  have hn := Spike.Lib.A64.RunsOff.runsNe_of_chk hp ck_chk _ hr (k + j) (by show lo ≤ k + j; omega)
    (by show k + j < hi; omega)
  exact ⟨hn _ (List.mem_cons_self ..), by
    simpa [Spike.Lib.A64.Flow.ofNat4_zero] using hn _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- **Off the clone's pc and the take site's.** -/
def OffC (exe : _root_.Executable) : Frag isaLSE2 := fun s _ =>
  s.st.2 ≠ cloneAt pfxM exe ∧ s.st.2 ≠ (_root_.Executable.labels exe).label Ret0.StackTake.siteL

/-- A node at `l + 4k` in the runs is off the clone's pc. -/
theorem nodeW_offC {n : ND} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) (h : ckIn l k 1 = true) :
    NodeW (OffC exe) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ => ⟨by
    show _ ∧ _
    rw [hpc, he]
    simpa using ck_ne hp h (j := 0) (by decide), fun _ h => h⟩

/-- A node at a label in the runs is off the clone's pc. -/
theorem nodeW_offC0 {n : ND} {l : Label} (he : n.pc = (_root_.Executable.labels exe).label l)
    (h : ckIn l 0 1 = true) : NodeW (OffC exe) (fun _ _ => False) exe endPc R F n :=
  nodeW_offC hp (k := 0) (by rw [he, Spike.Lib.A64.Flow.ofNat4_zero]) h

/-- A block node at `l + 4k` whose instructions are in the runs is off the
clone's pc. -/
theorem blkW_offC {n : ND} {blk : List Directive} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) (h : ckIn l k blk.length = true) :
    BlkW (OffC exe) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ j hj _ _ _ => ⟨by
    show _ ∧ _
    rw [he, Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add]
    exact ck_ne hp h hj, fun _ h => h⟩

/-- A block node at a label whose instructions are in the runs is off the
clone's pc. -/
theorem blkW_offC0 {n : ND} {blk : List Directive} {l : Label} (he : n.pc = (_root_.Executable.labels exe).label l)
    (h : ckIn l 0 blk.length = true) : BlkW (OffC exe) (fun _ _ => False) exe endPc R F n blk :=
  blkW_offC hp (k := 0) (by rw [he, Spike.Lib.A64.Flow.ofNat4_zero]) h

/-- One node or block of `WcMidW` off the clone's pc. -/
local macro "offc" : tactic =>
  `(tactic| first
    | exact nodeW_offC hp rfl (by decide +kernel)
    | exact nodeW_offC0 hp rfl (by decide +kernel)
    | exact blkW_offC hp rfl (by decide +kernel)
    | exact blkW_offC0 hp rfl (by decide +kernel))

/-- **`WcMidW`'s states are off the clone's pc**, with no outside moves:
every node of `wc_main` from `.sp0 + 16` to the `svc` and of its callees
is at a pc of `ckRuns`. -/
theorem wcMidW_offC {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidW (OffC exe) (fun _ _ => False) exe endPc R F F₂ ms J0 S Q := by
  refine ⟨⟨?_, ?_, fun g _ i => ?_⟩, fun c0 cA m fr _ => ⟨?_, fun g _ i => ?_⟩, fun c0 cA m fr _ => ⟨?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  case refine_3 => cases i <;> dsimp only [ReserveW] <;> offc
  case refine_5 => cases i <;> dsimp only [TcbWG] <;> offc
  all_goals offc

end Off

/-! ## `h1`'s outside move -/

/-- **`WcMidW` at the take of the site's range or a refusal**, the states
off the clone's pc and the take's pc `a`, from `WcMidW` at a take at `a`
(`wcMidW_wcG` at `PhRec.K L rK`): no take at `a` moves a state, so it is
off `a`; every state is off the clone's pc (`wcMidW_offC`), where only the
refusal `Cl` is (`hCl`). -/
theorem wcMidW_k1 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeProg kp) {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isaLSE2}
    {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {W : Frag isaLSE2} {a : Int64}
    {rK : Scc.Sem.Range} {Cl : State → Prop} (hCl : ∀ s, Cl s → pcOf s = (cloneAt pfxM exe).toBitVec.toNat)
    (h : WcMidW W (TakeK a rK) exe endPc R F F₂ ms J0 S Q) :
    WcMidW (fun s c => W s c ∧ pcOf s ≠ (cloneAt pfxM exe).toBitVec.toNat ∧ pcOf s ≠ a.toBitVec.toNat)
      (TakeCKS a Cl) exe endPc R F F₂ ms J0 S Q :=
  WcMidW.mapWK (fun _ _ ⟨hW, hc, _⟩ hk =>
      ⟨⟨hW, pcOf_ne hc, pcOf_ne (takeK_pc hk)⟩, takeCKS_none hCl (takeK_pc hk) (pcOf_ne hc)⟩)
    (WcMidW.and h (wcMidW_offC hp))

/-- **`WcMidW` at the take of the site's range or a refusal**, the states
off the clone's pc and the take site's (`wcMidW_offC`): only a refusal at
`Cl` (`hCl`, at the clone's pc) or a take at the site moves a state. -/
theorem wcMidW_k1S {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeProg kp) {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isaLSE2}
    {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {Cl : State → Prop}
    (hCl : ∀ s, Cl s → pcOf s = (cloneAt pfxM exe).toBitVec.toNat) :
    WcMidW (fun s _ => pcOf s ≠ (cloneAt pfxM exe).toBitVec.toNat ∧
        pcOf s ≠ ((_root_.Executable.labels exe).label Ret0.StackTake.siteL).toBitVec.toNat)
      (TakeCKS ((_root_.Executable.labels exe).label Ret0.StackTake.siteL) Cl) exe endPc R F F₂ ms J0 S Q :=
  WcMidW.mapWK (fun _ _ ⟨hc, ha⟩ _ => ⟨⟨pcOf_ne hc, pcOf_ne ha⟩, takeCKS_none hCl ha (pcOf_ne hc)⟩)
    (wcMidW_offC hp)

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcMidW.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcMidW.mapWK

/-- info: 'Spike.Lib.A64.Flow.WakeWc.takeCKS_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.takeCKS_none

/-- info: 'Spike.Lib.A64.Flow.WakeWc.ck_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.ck_ne

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wcMidW_offC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wcMidW_offC

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wcMidW_k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wcMidW_k1

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wcMidW_k1S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wcMidW_k1S
