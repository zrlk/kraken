/-
**wake.w's `wc_main` from inside its allocator just past the counter's
add, the thread pointer kept** (x86-64): `wake_wc_entry_segW`'s tail from a
state of `scc_rt_alloc`'s `c2` (just past the counter's `lock xadd`) of a
box call from `wc_main` returning to `.Lwc_main.x0`, to the allocator's
heap abort. The allocator's rest (`Alloc.seg_allocBW_at` at `c2`), its
return resumed in `wc_main`'s frame (`seg_resumeW`, the caller known
through `WcCtx`), then `.x18` (`wake_wc_sp0_segW`), all at `tpXa ms t`
inside `NoSetFsW (tpG t W) K` (`hWp`, `hWs`), the thread pointer kept
(`KeepTP.SegW.keepTP'`).

- `wake_wc_c2_segW`: the statement.

x86-64 twin of `Spike/Lib/A64WakeWcN4.lean` (namespace
`Spike.Lib.X64.Flow.WakeWc`).

**Where x86-64 differs from AArch64**:
- the allocator's node just past the counter's add is `Alloc.AN.c2` (A64
  `.n4`), and the allocator's segment from any node is already
  `Alloc.seg_allocBW_at` (A64 adds `seg_allocB_ofW_at`), so there is no
  `seg_allocB_ofW_at` here;
- the box call returns to `.Lwc_main.x0` (A64 `.L21_wc_main.sp0`); the
  allocator's region `wAR R = R.callee (-80) (-160) 8` with
  `CallerCells R (-80) (-160) 8` (A64 `… 0`), so `8 ≤ R.hi` and no
  alignment premise (A64 `hal`, `0 ≤ R.hi`);
- `wc_main`'s exits `wX` take the region `R` (`%rbp` at `R.addr (-8)` at
  `.x18`); the heap abort's return-address slot is `-240`;
- the box's landing (`hxa`) is on `R.fp (-8)`, the frame based at the saved
  `%rbp`; the thread pointer is `fsBase`, kept by `KeepTP.SegW.keepTP'`
  (A64 `SegW.keepTPN'`).
-/
import Spike.Lib.X64WakeWcMain
import Spike.Lib.X64CallResume
import Spike.Lib.X64WakeLand3

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Alloc (Call AllocW)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)

section C2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {q : Call}

/-- **`wc_main` from its allocator's `c2` is one segment inside `W`, the
thread pointer kept**, in any valid layout of `wakeCells`: from a state of
the allocator's `c2` (just past the counter's add) for a box call `q`
returning to `.Lwc_main.x0` (`hq`, `hra`), in the allocator's region under
`WcPreW.alloc`'s frame condition, with `TP t`, to the allocator's heap
abort with `TP t`. The box's landing is the `xa` exit (`hxa`). The other
premises are `wake_wc_entry_segW`'s, `hmem` at the call `q`. -/
theorem wake_wc_c2_segW {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop}
    (hWp : WcPreW (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J0 J0)
    (hWs : WcSp0W (NoSetFsW (tpG t W) K) K exe endPc R F (tpXa ms t) J0)
    (hq : q.OKB ms (_root_.Executable.labels exe).label)
    (hra : q.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x0").toBitVec)
    (hmem : ∀ a : BitVec 64,
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
    SegW W K p lbl ms
      (fun s c => At exe endPc (wAR R) (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧
          WcCtx ms (_root_.Executable.labels exe).label R J0 q m)
        (Alloc.N (_root_.Executable.labels exe).label ms q .c2) s c ∧ TP t s)
      (fun s c => At exe endPc R F (wX ms (_root_.Executable.labels exe).label R J0 .abort) s c ∧ TP t s) := by
  let lab := (_root_.Executable.labels exe).label
  have hqt : q.OKB (tpXa ms t) lab := okb_tpXa hq
  have hR' : (wAR R).OK := Region.callee_ok hR (by show R.lo ≤ -80 + -160; omega) (by decide)
    (by show (-80 : Int) < R.hi; omega) (by show (-80 : Int) + 8 ≤ R.hi; omega)
  -- the allocator's rest from `c2`
  have hA := Alloc.seg_allocBW_at (p := p) (lbl := lbl) hp hend wake_alloc
    (Spike.Lib.X64.WakePh.Land.fstable_wAR (ms := tpXa ms t) (lab := lab) (J := J0) (q := q) hR hF hlo hhi)
    hR' (by simp [Region.callee]) (by simp [Region.callee]) hqt (fun a ha m hm => hmem a ha m hm.1)
    (hWp.alloc q hqt hra) .c2
  -- its return resumed in `wc_main`'s frame
  have hres := seg_resumeW (N := fun e : Empty => e.elim) (E := wX (tpXa ms t) lab R J0) (F₂ := F)
    (M := fun _ => True)
    (PC := fun σC => ∃ c, (wN lab R J0 .call).J σC c ∧ (Alloc.N lab (tpXa ms t) q .e).J (enter (-80) σC) c)
    (hA.mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    (fun m ⟨h1, _, mC, σC', c', hA', hJ1, hJ2, hK'⟩ => ⟨h1, mC, σC', ⟨-80, []⟩, hK', hA', c', hJ1, hJ2⟩)
    (fun _ h _ => h) ?_
  · have hsp0 := wake_wc_sp0_segW (p := p) (lbl := lbl) (ms := tpXa ms t) (W := NoSetFsW (tpG t W) K)
      (Q := fun _ _ => False) hp hend hF hR (by omega) hhi hWs (fun q h => hbox ⟨q.1, okb_of_tpXa q.2⟩ h)
      (fun q h o h1 h2 => hcell ⟨q.1, okb_of_tpXa q.2⟩ h o h1 h2)
      (fun l A s c hl h ht => hxa l A s c hl (at_bX_of_tpXa h) ht)
    have hin := (hres.mono_post (Q' := fun s c => At exe endPc R F (wX (tpXa ms t) lab R J0 .x18) s c ∨
      At exe endPc R F (wX (tpXa ms t) lab R J0 .abort) s c) fun s c h => by
        rcases h with ⟨e, -⟩ | ⟨y, h⟩
        · exact e.elim
        · cases y
          · exact .inl h
          · exact .inr h).seq_left hsp0
    refine ((KeepTP.SegW.keepTP' hK hin (fun _ _ hw => hw.2.1) (fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim)
      fun _ _ hw ht => hw.1 ht).mono_pre fun s c h => h).mono_post ?_
    rintro s c ⟨h | h, ht⟩
    · exact h.elim
    · exact ⟨at_abort_of_tpXa h, ht⟩
  -- the allocator's exits land at `wc_main`'s
  rintro x σx c' σC hx ⟨c, ⟨⟨σe, hJe, h0', h8, h16⟩, hb, -, -, -, -⟩, ⟨hc, hfp, -⟩⟩
  have hsl : ∀ k, ¬ (wAR R).Off (k - -80) → (leave (wAR R) (-80) σC σx).slot k = σC.slot k :=
    fun k hn => by simp only [leave]; exact ite_eq_right hn
  cases x
  · have hx' := hx
    simp only [Alloc.EB] at hx'
    obtain ⟨o, -, -, -, -, hbx⟩ := hx'
    refine .inr ⟨WX.x18, ?_, by show SO.le ⟨-72, []⟩ ⟨-80 + 8, []⟩ = true; decide, ⟨q, hqt⟩,
      ⟨σe, hc ▸ hJe, ?_, ?_, ?_⟩, ?_, ?_⟩
    · show lab ".Lwc_main.x0" = Int64.ofBitVec q.ra
      rw [hra, int64_ofBitVec_toBitVec]
    · rw [hsl 0 (by simp only [Region.Off, Region.callee]; omega), h0']
    · rw [hsl (-8) (by simp only [Region.Off, Region.callee]; omega), h8]
    · rw [hsl (-16) (by simp only [Region.Off, Region.callee]; omega), h16]
    · rw [← hb]
      simp only [Reg64s.get64]
      rw [show (leave (wAR R) (-80) σC σx).regs = σx.regs from rfl, hbx, ← hfp]; rfl
    · exact hx
  · obtain ⟨h2, hfull, hs⟩ := hx
    refine .inr ⟨WX.abort, rfl, by show SO.le ⟨-240, []⟩ ⟨-80 + -160, []⟩ = true; decide, h2, ?_,
      ⟨q, hqt⟩, hfull, σe, hc ▸ hJe⟩
    show (leave (wAR R) (-80) σC σx).slot (-240) = _
    simp only [leave]
    rw [ite_eq_left (by simp only [Region.Off, Region.callee]; omega)]
    exact hs

end C2

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_c2_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_c2_segW
