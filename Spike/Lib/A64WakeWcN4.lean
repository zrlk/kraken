/-
**wake.w's `wc_main` from inside its allocator's `n4`, the thread pointer
kept** (AArch64): `wake_wc_entry_segW`'s tail from a state of
`scc_rt_alloc`'s `n4` (just past the counter's add) of a box call from
`wc_main` returning to `.sp0`, to the allocator's heap abort. The
allocator's rest (`seg_allocB_ofW_at` at `n4`), its return resumed in
`wc_main`'s frame (`seg_resumeW`, the caller known through `WcCtx`), then
`.sp0` (`wake_wc_sp0_segW`), all at `tpXa ms t` inside `NoMsrW (tpG t W) K`
(`hWp`, `hWs`), the thread pointer kept (`SegW.keepTPN'`).

- `seg_allocB_ofW_at`: `seg_allocB_ofW` from any allocator node `i0`.
- `wake_wc_n4_segW`: the statement.
-/
import Spike.Lib.A64WakeWcMain
import Spike.Lib.A64CallResume
import Spike.Lib.A64WakeWcPreG
import Spike.Lib.A64WakeLand3

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Spike.Lib.A64.KeepTP (TP tpXa)

section N4

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {q : Call}

/-- **`scc_rt_alloc` at a box allocation from its node `i0`** is one
segment inside `W` (`seg_allocB_ofW` from any node). -/
theorem seg_allocB_ofW_at {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hW : AllocW ms q W K exe endPc R F) (i0 : Alloc.AN) :
    SegW W K p lbl ms (At exe endPc R F (Alloc.N (_root_.Executable.labels exe).label ms q i0))
      (fun s c => ∃ x, At exe endPc R F (Alloc.EB (_root_.Executable.labels exe).label ms q x) s c) := by
  have hcode := Spike.Lib.A64.Flow.alloc_code (ms := ms) (q := q) hp hend hprog
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap⟩ := hprog
  exact Alloc.seg_allocBW_at hF hR hal hlo hhi hq hcode
    (by rw [label_labelGap hp hgap]; simp only [Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
    hmem hW i0

/-- **`wc_main` from its allocator's `n4` is one segment inside `W`, the
thread pointer kept**, in any valid layout of `wakeProg`: from a state of
the allocator's `n4` for a box call `q` returning to `.sp0` (`hq`, `hra`),
in the allocator's region under `WcPreW.alloc`'s frame condition, with
`TP t`, to the allocator's heap abort with `TP t`. The box's landing is the
`xa` exit (`hxa`). The other premises are `wake_wc_entry_segW`'s, `hmem` at
the call `q`. -/
theorem wake_wc_n4_segW {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop}
    (hWp : WcPreW (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J0)
    (hWs : WcSp0W (NoMsrW (tpG t W) K) K exe endPc R F (tpXa ms t) J0)
    (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hra : q.ra = ((_root_.Executable.labels exe).label ".L21_wc_main.sp0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) → BoxW lbl q.1)
    (hcell : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, J0 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms
      (fun s c => At exe endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 0 m ∧
          WcCtx ms (_root_.Executable.labels exe).label R J0 q m)
        (Alloc.N (_root_.Executable.labels exe).label ms q .n4) s c ∧ TP t s)
      (fun s c => At exe endPc R F (wX ms (_root_.Executable.labels exe).label J0 .abort) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hqt : q.OKB (tpXa ms t) lab := okb_tpXa hq
  obtain ⟨hR', hal'⟩ := Spike.Lib.A64.WakePh.WcW.wAR_ok hR hal hlo hhi
  -- the allocator's rest from `n4`
  have hA := seg_allocB_ofW_at (p := p) (lbl := lbl) hp hend wake_alloc
    (Spike.Lib.A64.WakePh.Land.fstable_wAR (ms := tpXa ms t) (lab := lab) (J := J0) (q := q) hR hF hlo hhi)
    hR' hal' (by simp [Region.callee]) (by simp [Region.callee]) hqt (fun a ha m hm => hmem a ha m hm.1)
    (hWp.alloc q hqt hra) .n4
  -- its return resumed in `wc_main`'s frame
  have hres := seg_resumeW (N := fun e : Empty => e.elim) (E := wX (tpXa ms t) lab J0) (F₂ := F)
    (M := fun _ => True)
    (PC := fun σC => ∃ c, (wN lab J0 .call).J σC c ∧ (Alloc.N lab (tpXa ms t) q .e).J (enter (-80) σC) c)
    (hA.mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    (fun m ⟨h1, _, mC, σC', c', hA', hJ1, hJ2, hK'⟩ => ⟨h1, mC, σC', ⟨-80, []⟩, hK', hA', c', hJ1, hJ2⟩)
    (fun _ h _ => h) ?_
  · have hsp0 := wake_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoMsrW (tpG t W) K)
      (Q := fun _ _ => False) hp hend hF hR hal (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
      (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
      (fun l A s c hl h ht => hxa l A s c hl (at_bX_of_tpXa h) ht)
    have hin := (hres.mono_post (Q' := fun s c => At exe endPc R F (wX (tpXa ms t) lab J0 .sp0) s c ∨
      At exe endPc R F (wX (tpXa ms t) lab J0 .abort) s c) fun s c h => by
        rcases h with ⟨e, -⟩ | ⟨y, h⟩
        · exact e.elim
        · cases y
          · exact .inl h
          · exact .inr h).seq_left hsp0
    refine ((SegW.keepTPN' hK hin fun _ _ h ht => h ht).mono_pre fun s c h => h).mono_post ?_
    rintro s c ⟨h | h, ht⟩
    · exact h.elim
    · exact ⟨at_abort_of_tpXa h, ht⟩
  -- the allocator's exits land at `wc_main`'s
  rintro x σx c' σC hx ⟨c, ⟨⟨σe, hJe, h16, h8, h80⟩, -, -, -, h30⟩, ⟨hc, -, h30', -⟩⟩
  have hsl : ∀ k, ¬ (wAR R).Off (k - -80) → (leave (wAR R) (-80) σC σx).slot k = σC.slot k :=
    fun k hn => by simp only [leave]; exact ite_eq_right hn
  cases x
  · refine .inr ⟨WX.sp0, ?_, rfl, ⟨q, hqt⟩, ⟨σe, hc ▸ hJe, ?_, ?_, ?_⟩, hx⟩
    · show lab ".L21_wc_main.sp0" = Int64.ofBitVec q.ra
      rw [hra, int64_ofBitVec_toBitVec]
    · rw [hsl (-16) (by simp only [Region.Off, Region.callee]; omega), h16]
    · rw [hsl (-8) (by simp only [Region.Off, Region.callee]; omega), h8]
    · rw [hsl (-80) (by simp only [Region.Off, Region.callee]; omega), h80]
  · obtain ⟨h2, h30x, hfull⟩ := hx
    exact .inr ⟨WX.abort, rfl, rfl, h2, h30x, ⟨q, hqt⟩, hfull, σe, hc ▸ hJe⟩

end N4

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.seg_allocB_ofW_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.seg_allocB_ofW_at

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_n4_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_n4_segW
