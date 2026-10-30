/-
**wake.w's `wc_main` from its entry, the thread pointer kept** (AArch64,
the pre-spawn consumer): `wake_wc_pre_segW` then `wake_wc_sp0_segW` proved
at `tpXa ms t` inside `NoMsrW W K`, as one segment
inside `W` at `ms` with `TPIDR_EL0 = t` at its exits and at the box's
landing (`ms.xa`, `hxa`), where `A64WakeWcHat.wake_wc_mid_hatW` continues;
and the facts the caller's `scc_rt_main` gives `wc_main`'s entry.

- `at_bX_of_tpXa`, `at_abort_of_tpXa`: the nodes at `tpXa ms t` at `ms`;
- `tp_of_at`: a state at a node whose invariant fixes the thread pointer;
- `wake_wc_entry_segW`: `wc_main`'s entry to its heap abort, the box's
  landing (with `TP t`) the `xa` exit;
- `wJ0_tp`: `wc_main`'s entry (`WakeM.wJ0`) has the thread pointer of
  `scc_rt_main`'s entry invariant;
- `wR_hup`, `wR_hfit`: `wc_mid_hat`'s `hup`, `hfit` at `wc_main`'s region
  (`WakeM.wR`) from its frame condition (`WakeM.wF`) and the caller's `R.OK`.
-/
import Spike.Lib.A64WakeWcHat
import Spike.Lib.A64AllocG

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (LimOk)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.Flow.WakeM (wJ wNC wJ0 wR wF)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (NoMsrAt TP tpXa)

/-! ## `tpXa` back to `ms` -/

/-- **The box's landing at `tpXa` is at `ms`** (`at_bX_tpXa`'s converse). -/
theorem at_bX_of_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl} (h : At exe endPc R F (bX (tpXa ms t) (_root_.Executable.labels exe).label J0 l A) s c) :
    At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_of_tpXa q.2⟩, h1, h2, h3⟩

/-- **The allocator's heap abort at `tpXa` is at `ms`**. -/
theorem at_abort_of_tpXa {ms : MemSide isaLSE2} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (wX (tpXa ms t) (_root_.Executable.labels exe).label J0 .abort) s c) :
    At exe endPc R F (wX ms (_root_.Executable.labels exe).label J0 .abort) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, q, hq, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, h0, h30, ⟨q.1, okb_of_tpXa q.2⟩, hq, hJ⟩

/-- **A state at a node whose invariant fixes the thread pointer has it**. -/
theorem tp_of_at {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {t : UInt64} (ht : ∀ σ c, n.J σ c → σ.regs.TPIDR_EL0 = t) {s : State} {c : Ctl}
    (h : At exe endPc R F n s c) : TP t s := by
  obtain ⟨-, -, -, -, σ, hA, -, hJ⟩ := h
  show s.st.1.regs.TPIDR_EL0 = t
  rw [hA.regs]; exact ht σ c hJ

/-! ## `W` guarded by the thread pointer -/

/-- **`W` at the states with thread pointer `t`** (`hWp`/`hWs`'s predicate). -/
abbrev tpG (t : UInt64) (W : Frag isaLSE2) : Frag isaLSE2 := fun s c => TP t s → W s c

section Mono

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}
  {W1 W2 : Frag isaLSE2} {K : State → State → Prop}

/-- `WcPreW` inside a weaker predicate. -/
theorem WcPreW.mono_W {J0 Jc : AS → Ctl → Prop} (h : WcPreW W1 K exe endPc R F ms J0 Jc)
    (hw : ∀ s c, W1 s c → W2 s c) : WcPreW W2 K exe endPc R F ms J0 Jc :=
  have hb : ∀ {n b}, BlkW W1 K exe endPc R F n b → BlkW W2 K exe endPc R F n b :=
    fun h => A64.AllocG.BlkW.imp h BlkW.triv fun s c h _ => hw s c h
  ⟨⟨hb h.pro.w0, A64.AllocG.NodeW.imp h.pro.w1 NodeW.triv fun s c h _ => hw s c h, hb h.pro.w2, hb h.pro.w3⟩,
    hb h.e, fun q h1 h2 => A64.AllocG.AllocW.imp (h.alloc q h1 h2) (Alloc.AllocW.triv ms q) fun s c h _ => hw s c h⟩

/-- `WcSp0W` inside a weaker predicate. -/
theorem WcSp0W.mono_W {J0 : AS → Ctl → Prop} (h : WcSp0W W1 K exe endPc R F ms J0)
    (hw : ∀ s c, W1 s c → W2 s c) : WcSp0W W2 K exe endPc R F ms J0 :=
  ⟨A64.AllocG.BlkW.imp h.b BlkW.triv fun s c h _ => hw s c h, A64.AllocG.NodeW.imp h.st NodeW.triv fun s c h _ => hw s c h⟩

/-- **The unguarded `hWp` gives the guarded one**. -/
theorem WcPreW.of_unguarded {t : UInt64} {W : Frag isaLSE2} {J0 Jc : AS → Ctl → Prop}
    (h : WcPreW (NoMsrW W K) K exe endPc R F ms J0 Jc) : WcPreW (NoMsrW (tpG t W) K) K exe endPc R F ms J0 Jc :=
  h.mono_W fun _ _ h => ⟨fun _ => h.1, h.2⟩

/-- **The unguarded `hWs` gives the guarded one**. -/
theorem WcSp0W.of_unguarded {t : UInt64} {W : Frag isaLSE2} {J0 : AS → Ctl → Prop}
    (h : WcSp0W (NoMsrW W K) K exe endPc R F ms J0) : WcSp0W (NoMsrW (tpG t W) K) K exe endPc R F ms J0 :=
  h.mono_W fun _ _ h => ⟨fun _ => h.1, h.2⟩

end Mono

/-! ## `wc_main`'s entry to the box's landing -/

section Entry

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from its entry is one segment inside `W`, the thread
pointer kept**, in any valid layout of `wakeProg`: `wake_wc_pre_segW`, then
`wake_wc_sp0_segW` at its allocator's return, both at `tpXa ms t` inside
`NoMsrW (tpG t W) K` (`hWp`, `hWs`: `W` needed only at thread pointer `t`), the
thread pointer `t` at the entry (`hJ0tp`; `SegW.keepTPN'`). The segment's only exit is the
allocator's heap abort; the box's landing `bX l A` with `TP t` is the
`xa` exit (`hxa`: the instance's `ms.xa` holds `wake_wc_mid_hatW`'s
entry). The other premises are `wake_wc_pre_segW`'s and
`wake_wc_sp0_segW`'s at `ms`. -/
theorem wake_wc_entry_segW {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hJ0tp : ∀ σ c, J0 σ c → σ.regs.TPIDR_EL0 = t)
    (hWp : WcPreW (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J0)
    (hWs : WcSp0W (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
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
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => At exe endPc R F (wX ms (_root_.Executable.labels exe).label J0 .abort) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hpre := wake_wc_pre_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
    hp hend hF hR hal hlo hhi hWp (fun σ c h => { hlim σ c h with })
    (fun σ c h => let ⟨q, hq1, hq2⟩ := hq σ c h; ⟨q, okb_tpXa hq1, hq2⟩)
    (fun q hq a ha m hm => hmem q (okb_of_tpXa hq) a ha m hm)
  have hsp0 := wake_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
    (Q := fun _ _ => False) hp hend hF hR hal (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
    (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
    (fun l A s c hl h ht => hxa l A s c hl (at_bX_of_tpXa h) ht)
  have hin := (hpre.mono_post (Q' := fun s c => At exe endPc R F (wX (tpXa ms t) lab J0 .sp0) s c ∨
    At exe endPc R F (wX (tpXa ms t) lab J0 .abort) s c) fun s c ⟨y, h⟩ => by
      cases y
      · exact .inl h
      · exact .inr h).seq_left hsp0
  refine ((SegW.keepTPN' hK hin fun _ _ h ht => h ht).mono_pre fun s c h => ⟨h, tp_of_at hJ0tp h⟩).mono_post ?_
  rintro s c ⟨h | h, ht⟩
  · exact h.elim
  · exact ⟨at_abort_of_tpXa h, ht⟩

end Entry

/-! ## The caller's facts at `wc_main`'s entry -/

/-- **`wc_main`'s entry keeps `scc_rt_main`'s thread pointer**: at
`WakeM.wJ0` of the call node `wNC` over `J`, the thread pointer is any
`J`-state's (`hJ`). -/
theorem wJ0_tp {lab : Label → Int64} {J : AS → Ctl → Prop} {t : UInt64}
    (hJ : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = t) {σC σ : AS} {c : Ctl} (h : wJ0 (wNC lab J).J σC σ c) :
    σ.regs.TPIDR_EL0 = t := by
  obtain ⟨rfl, ⟨σe, hJe, -, -, -, -, h5⟩, -, -⟩ := h
  exact h5.trans (hJ σe c hJe)

/-- **`wc_mid_hat`'s two cells above the base at `wc_main`'s region**: under
`WakeM.wF`, the caller's cells at `-48`, `-40` (offsets `0`, `8` of
`wR R D`) lie outside the callee's region, as at the call (`CKept`), where
the caller's state reads them (`Abs`). -/
theorem wR_hup {R : Region} {D : Int} {F : MachineData → Prop} {m0 m : MachineData} {σC : AS}
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (h : wF R D F m0 σC m) :
    ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt m.dmem ((wR R D).addr k) 8).isSome := by
  obtain ⟨-, hK, hA⟩ := h
  intro k h8 h0 h16
  have hoff : R.Off (-48 + k) := ⟨by omega, by omega, by omega⟩
  rw [Region.callee_addr, hK (-48 + k) hoff fun ⟨_, _, h3⟩ => by simp only [Region.callee] at h3; omega]
  obtain ⟨j, hj, -⟩ := hA.slot (-48 + k) hoff
  rw [hj]; rfl

/-- **`wc_mid_hat`'s room at `wc_main`'s region**: its base is `48` below
the caller's, inside the caller's region. -/
theorem wR_hfit {R : Region} {D : Int} (hR : R.OK) (hlo : R.lo ≤ -48 - D) (hD : 0 ≤ D) (hhi : 0 ≤ R.hi) :
    ((wR R D).base.toNat : Int) + 16 ≤ 2 ^ 64 := by
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -48 + -D by omega) (by omega)
    (show (-48 : Int) < R.hi by omega)
  have := hR.hi
  show ((R.callee (-48) (-D) 0).base.toNat : Int) + 16 ≤ 2 ^ 64
  rw [hb]; omega

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_entry_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_entry_segW

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcPreW.of_unguarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcPreW.of_unguarded

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcSp0W.of_unguarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcSp0W.of_unguarded

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wJ0_tp' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wJ0_tp

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wR_hup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wR_hup

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wR_hfit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wR_hfit
