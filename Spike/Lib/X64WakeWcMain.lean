/-
**wake.w's `wc_main` from its entry, the thread pointer kept** (x86-64;
twin of `Spike/Lib/A64WakeWcMain.lean`, the pre-spawn consumer):
`wake_wc_pre_segW` then `wake_wc_sp0_segW` proved at `tpXa ms t` inside
`NoSetFsW W K`, as one segment inside `W` at `ms` with `fsBase = t` at its
exits and at the box's landing (`ms.xa`, `hxa`), where
`X64WakeWcHat.wake_wc_mid_hatW` continues; and the facts the caller's
`scc_rt_main` gives `wc_main`'s entry.

- `at_bX_of_tpXa`, `at_abort_of_tpXa`: the nodes at `tpXa ms t` at `ms`;
- `WcPreW.mono_W`, `WcSp0W.mono_W`, `WcPreW.of_unguarded`,
  `WcSp0W.of_unguarded`: the node obligations inside a weaker predicate,
  the unguarded ones as the guarded (`WakeTP.tpG`);
- `wake_wc_entry_segW`: `wc_main`'s entry to its heap abort, the box's
  landing (with `TP t`) the `xa` exit;
- `wJ0_tp`: `wc_main`'s entry (`WakeM.wJ0`) has the thread pointer of
  `scc_rt_main`'s entry invariant;
- `fp8_ok`: the landing's region `R.fp (-8)` (where `wake_wc_mid_hatW`
  runs) is a region with `F` stable, its bounds `R`'s shifted by `8`.

**Where this differs from AArch64**: `tpG` and `tp_of_at` are
`Spike.Lib.X64.WakeTP`'s (not redefined here). The thread pointer is
`fsBase`, so `NoMsrW` is `NoSetFsW` and `SegW.keepTPN'` is
`KeepTP.SegW.keepTP'` applied directly. The x86-64 `wake_wc_pre_segW` has no
alignment premise (`hal`), its `hlim` is stated at `fsBase + 8` and
`%rsp - 8 - 64` with no executable, and `8 ≤ R.hi` (the return address
cell); `wake_wc_sp0_segW`'s landing (`hxa`) is on `R.fp (-8)`, the frame
based at the saved `%rbp`. A64's `wR_hup`, `wR_hfit` (the room `upAS`
re-reads above a callee's region) have no counterpart:
`wake_wc_mid_hatW`'s region `R.fp (-8)` already reaches `[-64, 16)`
(`fp8_ok`: at `WakeM.wR R D`, `lo = 8 - D`, `hi = 16`).
-/
import Spike.Lib.X64WakeWcHat
import Spike.Lib.X64AllocG
import Spike.Lib.X64WakeTP
import Spike.Lib.X64WakeMain

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.WakeM (wJ wNC wJ0 wR wF)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64.WakeTP (tpG tp_of_at)

/-! ## `tpXa` back to `ms` -/

/-- **The box's landing at `tpXa` is at `ms`** (`at_bX_tpXa`'s converse). -/
theorem at_bX_of_tpXa {ms : MemSide isa} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl}
    (h : At exe endPc R F (bX (tpXa ms t) (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_of_tpXa q.2⟩, h1, h2, h3⟩

/-- **The allocator's heap abort at `tpXa` is at `ms`**. -/
theorem at_abort_of_tpXa {ms : MemSide isa} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (wX (tpXa ms t) (_root_.Executable.labels exe).label R J0 .abort) s c) :
    At exe endPc R F (wX ms (_root_.Executable.labels exe).label R J0 .abort) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h0, hs, q, hq, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, h0, hs, ⟨q.1, okb_of_tpXa q.2⟩, hq, hJ⟩

/-! ## `W` guarded by the thread pointer -/

section Mono

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}
  {W1 W2 : Frag isa} {K : State → State → Prop}

/-- `WcPreW` inside a weaker predicate. -/
theorem WcPreW.mono_W {J0 Jc : AS → Ctl → Prop} (h : WcPreW W1 K exe endPc R F ms J0 Jc)
    (hw : ∀ s c, W1 s c → W2 s c) : WcPreW W2 K exe endPc R F ms J0 Jc :=
  have hb : ∀ {n b}, BlkW W1 K exe endPc R F n b → BlkW W2 K exe endPc R F n b :=
    fun h => AllocG.BlkW.imp h BlkW.triv fun s c h _ => hw s c h
  ⟨⟨hb h.pro.w0, hb h.pro.w1, AllocG.NodeW.imp h.pro.w2 NodeW.triv fun s c h _ => hw s c h, hb h.pro.w3,
      hb h.pro.w4⟩,
    hb h.e, fun q h1 h2 => AllocG.AllocW.imp (h.alloc q h1 h2) (Alloc.AllocW.triv ms q) fun s c h _ => hw s c h⟩

/-- `WcSp0W` inside a weaker predicate. -/
theorem WcSp0W.mono_W {J0 : AS → Ctl → Prop} (h : WcSp0W W1 K exe endPc R F ms J0)
    (hw : ∀ s c, W1 s c → W2 s c) : WcSp0W W2 K exe endPc R F ms J0 :=
  ⟨AllocG.BlkW.imp h.b BlkW.triv fun s c h _ => hw s c h, AllocG.NodeW.imp h.st NodeW.triv fun s c h _ => hw s c h⟩

/-- **The unguarded `hWp` gives the guarded one**. -/
theorem WcPreW.of_unguarded {t : UInt64} {W : Frag isa} {J0 Jc : AS → Ctl → Prop}
    (h : WcPreW (NoSetFsW W K) K exe endPc R F ms J0 Jc) :
    WcPreW (NoSetFsW (tpG t W) K) K exe endPc R F ms J0 Jc :=
  h.mono_W fun _ _ h => ⟨fun _ => h.1, h.2⟩

/-- **The unguarded `hWs` gives the guarded one**. -/
theorem WcSp0W.of_unguarded {t : UInt64} {W : Frag isa} {J0 : AS → Ctl → Prop}
    (h : WcSp0W (NoSetFsW W K) K exe endPc R F ms J0) :
    WcSp0W (NoSetFsW (tpG t W) K) K exe endPc R F ms J0 :=
  h.mono_W fun _ _ h => ⟨fun _ => h.1, h.2⟩

end Mono

/-! ## `wc_main`'s entry to the box's landing -/

section Entry

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from its entry is one segment inside `W`, the thread
pointer kept**, in any valid layout of `wakeCells`: `wake_wc_pre_segW`, then
`wake_wc_sp0_segW` at its allocator's return, both at `tpXa ms t` inside
`NoSetFsW (tpG t W) K` (`hWp`, `hWs`: `W` needed only at thread pointer
`t`), the thread pointer `t` at the entry (`hJ0tp`; `KeepTP.SegW.keepTP'`).
The segment's only exit is the allocator's heap abort; the box's landing
`bX l A` on `R.fp (-8)` with `TP t` is the `xa` exit (`hxa`: the instance's
`ms.xa` holds `wake_wc_mid_hatW`'s entry). The other premises are
`wake_wc_pre_segW`'s and `wake_wc_sp0_segW`'s at `ms`. -/
theorem wake_wc_entry_segW {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hJ0tp : ∀ σ c, J0 σ c → σ.regs.fsBase = t)
    (hWp : WcPreW (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J0)
    (hWs : WcSp0W (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec))
    (hq : ∀ σ c, J0 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none →
      At exe endPc (R.fp (-8)) F (bX ms (_root_.Executable.labels exe).label J0 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (wX ms (_root_.Executable.labels exe).label R J0 .abort) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hpre := wake_wc_pre_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoSetFsW (tpG t W) K)
    hp hend hF hR hlo hhi hWp (fun σ c h => { hlim σ c h with })
    (fun σ c h => let ⟨q, hq1, hq2⟩ := hq σ c h; ⟨q, okb_tpXa hq1, hq2⟩)
    (fun q hq a ha m hm => hmem q (okb_of_tpXa hq) a ha m hm)
  have hsp0 := wake_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoSetFsW (tpG t W) K)
    (Q := fun _ _ => False) hp hend hF hR (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
    (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
    (fun l A s c hl h ht => hxa l A s c hl (at_bX_of_tpXa h) ht)
  have hin := (hpre.mono_post (Q' := fun s c => At exe endPc R F (wX (tpXa ms t) lab R J0 .x18) s c ∨
    At exe endPc R F (wX (tpXa ms t) lab R J0 .abort) s c) fun s c ⟨y, h⟩ => by
      cases y
      · exact .inl h
      · exact .inr h).seq_left hsp0
  refine ((KeepTP.SegW.keepTP' hK hin (fun _ _ hw => hw.2.1) (fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim)
    fun _ _ hw ht => hw.1 ht).mono_pre fun s c h => ⟨h, tp_of_at hJ0tp h⟩).mono_post ?_
  rintro s c ⟨h | h, ht⟩
  · exact h.elim
  · exact ⟨at_abort_of_tpXa h, ht⟩

end Entry

/-! ## The caller's facts at `wc_main`'s entry -/

/-- **`wc_main`'s entry keeps `scc_rt_main`'s thread pointer**: at
`WakeM.wJ0` of the call node `wNC` over `J`, the thread pointer is any
`J`-state's (`hJ`). -/
theorem wJ0_tp {lab : Label → Int64} {J : AS → Ctl → Prop} {t : UInt64}
    (hJ : ∀ σ c, J σ c → σ.regs.fsBase = t) {σC σ : AS} {c : Ctl} (h : wJ0 (wNC lab J).J σC σ c) :
    σ.regs.fsBase = t := by
  obtain ⟨rfl, ⟨σe, hJe, -, -, -, -, h5⟩, -, -, -⟩ := h
  exact h5.trans (hJ σe c hJe)

/-- **The box's landing region**: `R.fp (-8)`, the frame based at the
saved `%rbp`, is a region with `F` stable and `R`'s bounds shifted by `8`
(`wake_wc_mid_hatW`'s `hR`, `hF`, `hlo`, `hhi` from `wc_main`'s). -/
theorem fp8_ok {R : Region} {F : MachineData → Prop} (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -8)
    (hhi : -8 < R.hi) :
    (R.fp (-8)).OK ∧ FStable (R.fp (-8)) F ∧ (R.fp (-8)).lo = R.lo + 8 ∧ (R.fp (-8)).hi = R.hi + 8 :=
  ⟨Region.fp_ok hR hlo hhi, FStable.fp hR hlo hhi hF, by simp only [Region.fp, Region.callee]; omega,
    by simp only [Region.fp, Region.callee]; omega⟩

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_entry_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_entry_segW

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcPreW.of_unguarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcPreW.of_unguarded

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcSp0W.of_unguarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcSp0W.of_unguarded

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wJ0_tp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wJ0_tp

/-- info: 'Spike.Lib.X64.Flow.WakeWc.fp8_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.fp8_ok
