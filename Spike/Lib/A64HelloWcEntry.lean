/-
**hello.w's `wc_main` from its entry, the thread pointer kept, and its entry
facts from `wc_rodata`'s return** (AArch64 row 5h;
the twin of `A64WakeWcMain`'s `wake_wc_entry_segW` and of `A64WakeJ0` at
helloProg, frame 144): `hello_wc_pre_segW` then `hello_wc_sp0_segW` proved at
`tpXa ms t` inside `NoMsrW (tpG t W) K`, as one segment inside `W` at `ms`
with `TPIDR_EL0 = t` at its exit and at the box's landing (`ms.xa`, `hxa`).

hello's `scc_rt_main` calls `wc_rodata` before `wc_main`, so `wc_main`'s
entry invariant is `HelloM.wcJ0 (Hello1.mWC lab σC Jr).J σ1` (`hello_main_post_segW`'s
`hWc`): `wc_rodata`'s return invariant `Jr` (at `.sp0` after leaving its region),
the call keeping the registers. Unlike wake's (`wJ`, `sp` lowered by `48`), the
call node keeps `sp` and the thread pointer of `Jr`'s state, so the caller
premises are asked at `Jr` with `wc_main`'s own `sp - 144`.

- `at_bXH_of_tpXa`, `at_abortH_of_tpXa`: the nodes at `tpXa ms t` at `ms`;
- `hello_wc_entry_segW`: `wc_main`'s entry to its heap abort, the box's landing
  (with `TP t`) the `xa` exit;
- `wcJ0_inv`, `tp_wcJ0`, `lim_wcJ0`, `ctl_wcJ0`, `hj_wcJ0`, `loc_wcJ0`: the
  entry's facts from `Jr`'s (`ctl_wcJ0` also gives `WcWfS.wcPreW_WSH`'s
  `hc0J`/`hc1J`, `tp_wcJ0` its `htp`);
- `mem_wcF`, `cell_wcF`: the frame condition's from the caller's;
- `hello_wc_entry_segJr`: `hello_wc_entry_segW` at `wcJ0 … Jr`, `wcJ0 … Jr1`
  (`Jr1`: `Jr` after the entry block's local run), `wcR R D`, `wcF R D F0 m1 σ1`.
-/
import Spike.Lib.A64HelloWcSp0
import Spike.Lib.A64HelloMain
import Spike.Lib.A64WakeWcMain

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (LimOk)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW tpG tp_of_at okb_tpXa okb_of_tpXa)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (TP tpXa)

/-! ## `tpXa` back to `ms` -/

/-- **The box's landing at `tpXa` is at `ms`**. -/
theorem at_bXH_of_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl} (h : At exe endPc R F (bXH (tpXa ms t) (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_of_tpXa q.2⟩, h1, h2, h3⟩

/-- **The allocator's heap abort at `tpXa` is at `ms`**. -/
theorem at_abortH_of_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (wXH (tpXa ms t) (_root_.Executable.labels exe).label J1 .abort) s c) :
    At exe endPc R F (wXH ms (_root_.Executable.labels exe).label J1 .abort) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, q, hq, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, ⟨q.1, okb_of_tpXa q.2⟩, hq, hJ⟩

/-! ## `wc_main`'s entry to the box's landing -/

section Entry

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from its entry is one segment inside `W`, the thread pointer
kept**, in any valid layout of `helloProg`: `hello_wc_pre_segW`, then
`hello_wc_sp0_segW` at its allocator's return, both at `tpXa ms t` inside
`NoMsrW (tpG t W) K` (`hWp`, `hWs`), the thread pointer `t` at the entry
(`hJ0tp`; `SegW.keepTPN'`). The segment's only exit is the allocator's heap
abort; the box's landing `bXH l A` with `TP t` is the `xa` exit (`hxa`). The
other premises are `hello_wc_pre_segW`'s and `hello_wc_sp0_segW`'s at `ms`. -/
theorem hello_wc_entry_segW {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    {J0 J1 : AS → Ctl → Prop} (hJ0tp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = t)
    (hWp : WcPreWH (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J1)
    (hWs : WcSp0WH (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J1)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec))
    (hloc : ∀ σ c, J0 σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (wXH ms (_root_.Executable.labels exe).label J1 .abort) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hpre := hello_wc_pre_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
    hp hend hF hR hal hlo hhi hWp (fun σ c h => { hlim σ c h with }) hloc
    (fun σ c h => let ⟨q, hq1, hq2⟩ := hq σ c h; ⟨q, okb_tpXa hq1, hq2⟩)
    (fun q hq a ha m hm => hmem q (okb_of_tpXa hq) a ha m hm)
  have hsp0 := hello_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
    (Q := fun _ _ => False) hp hend hF hR hal (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
    (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
    (fun l A s c hl h ht => hxa l A s c hl (at_bXH_of_tpXa h) ht)
  have hin := (hpre.mono_post (Q' := fun s c => At exe endPc R F (wXH (tpXa ms t) lab J1 .sp0) s c ∨
    At exe endPc R F (wXH (tpXa ms t) lab J1 .abort) s c) fun s c ⟨y, h⟩ => by
      cases y
      · exact .inl h
      · exact .inr h).seq_left hsp0
  refine ((SegW.keepTPN' hK hin fun _ _ h ht => h ht).mono_pre fun s c h => ⟨h, tp_of_at hJ0tp h⟩).mono_post ?_
  rintro s c ⟨h | h, ht⟩
  · exact h.elim
  · exact ⟨at_abortH_of_tpXa h, ht⟩

end Entry

/-! ## The entry's facts from `wc_rodata`'s return -/

section Jr

variable {lab : Label → Int64} {σC σ1 : AS} {Jr : AS → Ctl → Prop}

/-- **An entry state is a `Jr` state's**: `sp` and the thread pointer kept,
the control the same (`mWC`; the call's `enter` moves only the cells). -/
theorem wcJ0_inv {σ : AS} {c : Ctl} (h : wcJ0 (mWC lab σC Jr).J σ1 σ c) :
    ∃ σx, Jr σx c ∧ σ.regs.SP = σx.regs.SP ∧ σ.regs.TPIDR_EL0 = σx.regs.TPIDR_EL0 := by
  obtain ⟨rfl, σx, hJ, -, -, -, -, -, hsp, htp, -⟩ := h
  exact ⟨σx, hJ, hsp, htp⟩

/-- **The thread pointer at the entry** (`hJ0tp`, `WcWfS.wcPreW_WSH`'s `htp`) from `Jr`'s. -/
theorem tp_wcJ0 {t : UInt64} (hJ : ∀ σ c, Jr σ c → σ.regs.TPIDR_EL0 = t) :
    ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c → σ.regs.TPIDR_EL0 = t :=
  fun _ _ h => let ⟨σx, hJx, _, htp⟩ := wcJ0_inv h; htp.trans (hJ σx _ hJx)

/-- **`hlim`**: the limit word at `Jr`'s thread pointer, bounded by `Jr`'s
`sp - 144` (`wc_main`'s frame), at the caller's `F0`. -/
theorem lim_wcJ0 {ms : MemSide isaLSE2} {F0 : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {D : Int} {m1 : MachineData}
    (h : ∀ σ c, Jr σ c → LimOk ms F0 exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec)) :
    ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c →
      LimOk ms (wcF R D F0 m1 σ1) exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec) := by
  intro σ c hJ
  obtain ⟨σx, hJx, hsp, htp⟩ := wcJ0_inv hJ
  have ht : tcbA σ.regs 8 = tcbA σx.regs 8 := by simp only [tcbA, htp]
  rw [ht, hsp]
  exact (h σx c hJx).mono fun _ hm => hm.1

/-- **A fact of the entry's control** (`hq`, `hc0J`) from `Jr`'s (the call keeps it). -/
theorem ctl_wcJ0 {P : Ctl → Prop} (h : ∀ σ c, Jr σ c → P c) : ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c → P c :=
  fun _ c hJ => let ⟨σx, hJx, _⟩ := wcJ0_inv hJ; h σx c hJx

/-- **The box's control is a `Jr` state's**. -/
theorem hj_wcJ0 {c : Ctl} (h : ∃ σ, wcJ0 (mWC lab σC Jr).J σ1 σ c) : ∃ σ, Jr σ c :=
  let ⟨_, hJ⟩ := h; let ⟨σx, hJx, _⟩ := wcJ0_inv hJ; ⟨σx, hJx⟩

/-- **`hloc`**: the entry block's local run from `Jr`'s to `Jr1`'s, the state kept. -/
theorem loc_wcJ0 {p : Prog} {Jr1 : AS → Ctl → Prop} (h : ∀ σ c, Jr σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c') :
    ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c → ∃ c', LocalRun p c c' ∧ wcJ0 (mWC lab σC Jr1).J σ1 σ c' := by
  rintro σ c ⟨rfl, σx, hJx, hr⟩
  obtain ⟨c', hl, hJ1⟩ := h σx c hJx
  exact ⟨c', hl, rfl, σx, hJ1, hr⟩

/-- **`hmem`** from the caller's `F0`. -/
theorem mem_wcF {ms : MemSide isaLSE2} {F0 : MachineData → Prop} {R : Region} {D : Int} {m1 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none) :
    ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, wcF R D F0 m1 σ1 m → Mem.loadInt m.dmem a 8 = none :=
  fun q hq a ha m hm => h q hq a ha m hm.1

/-- **`hcell`** from the caller's `F0`, at `Jr1`'s controls. -/
theorem cell_wcF {ms : MemSide isaLSE2} {F0 : MachineData → Prop} {R : Region} {D : Int} {m1 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : AGB ms ll, (∃ σ, Jr σ q.1.c0) → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none) :
    ∀ q : AGB ms ll, (∃ σ, wcJ0 (mWC lab σC Jr).J σ1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, wcF R D F0 m1 σ1 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none :=
  fun q hj o h1 h2 => ⟨(h q (hj_wcJ0 hj) o h1 h2).1, fun m hm => (h q (hj_wcJ0 hj) o h1 h2).2 m hm.1⟩

end Jr

/-! ## `hello_wc_entry_segW` at `scc_rt_main`'s call -/

/-- **`wc_main` from its entry at `scc_rt_main`'s call after `wc_rodata`**
(`hello_main_post_segW`'s `hWc`): `hello_wc_entry_segW` at
`J0 := wcJ0 (mWC lab σC Jr).J σ1`, `J1 := wcJ0 (mWC lab σC Jr1).J σ1`, the
region `wcR R D` and the frame condition `wcF R D F0 m1 σ1`, its caller
premises from `Jr`'s (the thread pointer `t`, the limit word bounded by
`sp - 144`, the entry block's local run to `Jr1`), `Jr1`'s (the box's call)
and `F0`'s (`hmem0`, `hcell0`). The other premises are
`hello_wc_entry_segW`'s. -/
theorem hello_wc_entry_segJr {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {D : Int} {F0 : MachineData → Prop} {m1 : MachineData} {σC σ1 : AS}
    {Jr Jr1 : AS → Ctl → Prop} {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable (wcR R D) (wcF R D F0 m1 σ1)) (hR : (wcR R D).OK) (hal : (wcR R D).base.toNat % 16 = 0)
    (hlo : (wcR R D).lo ≤ -304) (hhi : 0 ≤ (wcR R D).hi)
    (htp : ∀ σ c, Jr σ c → σ.regs.TPIDR_EL0 = t)
    (hWp : WcPreWH (NoMsrW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F0 m1 σ1) (tpXa ms t)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
    (hWs : WcSp0WH (NoMsrW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F0 m1 σ1) (tpXa ms t)
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1))
    (hlim : ∀ σ c, Jr σ c → LimOk ms F0 exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec))
    (hloc : ∀ σ c, Jr σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c')
    (hq : ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem0 : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → BoxW lbl q.1)
    (hcell0 : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
      (bXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
        l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩)
      (fun s c => At exe endPc (wcR R D) (wcF R D F0 m1 σ1)
        (wXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
          .abort) s c ∧ TP t s) :=
  hello_wc_entry_segW hK hp hend hF hR hal hlo hhi (tp_wcJ0 htp) hWp hWs (lim_wcJ0 hlim) (loc_wcJ0 hloc)
    (ctl_wcJ0 hq) (mem_wcF hmem0) (fun q h => hbox q (hj_wcJ0 h)) (cell_wcF hcell0) hxa

end Spike.Lib.A64.Flow.HelloWc

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segW

/-- info: 'Spike.Lib.A64.Flow.HelloWc.lim_wcJ0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.lim_wcJ0

/-- info: 'Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJr
