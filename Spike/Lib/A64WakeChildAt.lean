/-
**wake.w on AArch64: the child after the `clone` is at the stub's node**
(the spawn's child half): the thread `childAfter` gives
(`Spike.Lib.Handover.childAfter`, the handed range `r1` copied into its
empty private memory) is in the fragment `At … (childN …)` of
`Spike.Lib.A64.Flow.Worker.Wake.Child`, so `seg_childStub` runs it.

The region is the handed stack's top `r1.lo + r1.size` with offsets
`[lo, 0)` (`childR`), `lo ≤ 0` no deeper than the range; every word of it is
mapped (the handed bytes), and the frame condition is the child's first
memory outside the region (`DFrame`, stable: `FStable.dframe`). The worker's
words are the parent's `x9`/`x10`, the thread pointer `tls`, `sp` the top.

- `svcB`, `wake_svcIn`: the clone's `svc` (`cloneAt pfxM`) in wake's program.
- `childR`: the child's region.
- `loadInt_copyRange`: a word inside the copied range is mapped.
- `child_at`: the child after a `clone` whose stack range is handed is at
  `childN`.
- `clonePre_child_at`: from main's state at its `clone`
  (`Spike.Lib.WakePreA.ClonePre`) in a layout of `wakeProg`, the child is at
  `childN` with the worker's words `cA`/`meW`, the thread pointer `tls`, `sp`
  the top of `r1`.
-/
import Spike.Lib.A64WakeChild
import Spike.Lib.A64Handover
import Spike.Lib.WakePreA
import Scc.Sem.OwnDom

namespace Spike.Lib.A64.Flow.Worker.Wake.Child

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakePreA (cloneAt)

/-- The clone's `svc`. -/
def svcB : List Directive := parseAArch64("svc #0")

/-- The clone's `svc` in wake's program, 13 instructions past `.sp6`. -/
abbrev svcIn : Bool := blockAt wakeProg (pfxM ++ ".sp6") 13 svcB

theorem wake_svcIn : svcIn = true := by decide +kernel

/-- **The child's region**: offsets `[lo, 0)` below the stack top `top`. -/
def childR (top : Nat) (lo : Int) : Spike.Lib.Region := ⟨BitVec.ofNat 64 top, lo, 0⟩

/-- **A word inside the copied range is mapped.** -/
theorem loadInt_copyRange {src : _root_.Mem 64} {r : Range} {a : BitVec 64} (hr : r.lo + r.size ≤ 2 ^ 64)
    (h1 : r.lo ≤ a.toNat) (h2 : a.toNat + 8 ≤ r.lo + r.size) :
    (Mem.loadInt (copyRange src ∅ r) a 8).isSome = true := by
  simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff, List.forall_mem_map,
    List.mem_range]
  intro i hi
  rw [Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.mem_iff_isSome_getElem?, mem_copyRange]
  refine .inl ((mem_addrs_iff hr _).mpr ?_)
  have ha := a.isLt
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  unfold Range.contains
  omega

/-- **The child after the `clone` is at the stub's node**: a thread `t` at
the clone's `svc` (`cloneAt pfx exe`, a 4-byte cell there: `hcode`), whose
stack top `r1.lo + r1.size` ends the handed range `r1`, gives a child in
`At` of `childN` for the region `childR` (no deeper than `r1`), the frame
condition its first memory outside the region, the worker's words the
parent's `x9`/`x10`, the thread pointer `tls`, `sp` the top, any source
control `cW`. -/
theorem child_at {pfx : String} {exe : _root_.Executable} {endPc : Int64} {x : KState} {tid : Nat}
    {t : Thread isaLSE2} {r1 : Range} {tls : Nat} {lo : Int} {cW : Ctl}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (cloneAt pfx exe) svcB)
    (he : t.st.exe = exe) (hn : t.st.endPc = endPc) (hd : t.st.decls = {})
    (hpc : t.st.st.2 = cloneAt pfx exe)
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (htop : r1.lo + r1.size < 2 ^ 64) (hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) :
    At exe endPc (childR (r1.lo + r1.size) lo)
      (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1)
      (childN pfx (_root_.Executable.labels exe).label cW t.st.st.1.regs.X9.toBitVec
        t.st.st.1.regs.X10.toBitVec (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
      (childAfter abi x tid t (r1.lo + r1.size) tls).st cW := by
  have hc : (childAfter abi x tid t (r1.lo + r1.size) tls).st =
      { t.st with st := ({ t.st.st.1 with
          regs := { t.st.st.1.regs with X0 := 0, SP := UInt64.ofNat (r1.lo + r1.size), TPIDR_EL0 := UInt64.ofNat tls },
          dmem := copyRange t.st.st.1.dmem ∅ r1 }, nextPc t.st) } := by
    unfold childAfter; rw [hh]; rfl
  obtain ⟨d0, hd0⟩ : ∃ d, svcB[0]? = some d := ⟨_, rfl⟩
  have hcell : CellAt t.st d0 4 := by
    have := hcode t.st he hn 0 d0 hd0
    rw [ofNat4_zero, ← hpc] at this
    exact this
  have hnext := nextPc_of_cellAt hcell
  rw [hc]
  refine ⟨he, hn, hd, ?_, ⟨_, _, fun k => BitVec.ofInt 64 ((Mem.loadInt (copyRange t.st.st.1.dmem ∅ r1)
    ((childR (r1.lo + r1.size) lo).addr k) 8).getD 0)⟩, ⟨rfl, rfl, ?_, ?_⟩, DFrame.refl _ _, ?_⟩
  · show nextPc t.st = _
    rw [hnext, hpc]; rfl
  · intro r k h
    cases r with
    | SP =>
      simp only [SO.get, childN, Option.some.injEq] at h
      subst h
      show (UInt64.ofNat _).toBitVec = BitVec.ofNat 64 _ + BitVec.ofInt 64 0
      exact (BitVec.add_zero _).symm
    | reg xr => simp [SO.get, childN, lk] at h
  · intro k hk
    obtain ⟨-, hk1, hk2⟩ := hk
    have hR : (childR (r1.lo + r1.size) lo).OK := ⟨by simp [childR]; omega, by simp [childR]; omega⟩
    have ha := Spike.Lib.Region.addr_toNat_of hR (k := k) hk1 (by simp [childR] at hk2 ⊢; omega)
    simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop] at ha hk1 hk2
    have hs := loadInt_copyRange (src := t.st.st.1.dmem) (r := r1)
      (a := (childR (r1.lo + r1.size) lo).addr k) (by omega) (by simp only [childR] at *; omega)
      (by simp only [childR] at *; omega)
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨j, hj, by simp [hj]⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The child after main's `clone` is at the stub's node** (wake's layout
`hp`): main's state at the clone (`ClonePre`; `hX`: its runtime facts pin
the executable, its end and no declarations) gives the child, after the
clone hands it `r1`, in `At` of `childN` for `childR` (no deeper than
`r1`), with `cA`/`meW`/`tls` `ClonePre`'s. -/
theorem clonePre_child_at {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) {lo : Int} (hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) (cW : Ctl) :
    ∃ (th : Thread isaLSE2) (tls cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
      At exe endPc (childR (r1.lo + r1.size) lo)
        (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
        (childN pfxM (_root_.Executable.labels exe).label cW (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW)
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
        (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st cW := by
  obtain ⟨th, -, tls, cA, meW, -, hth, -, hpc, -, -, hcall, -, -, h9, h10, hheld, -, -, -, hXs, -⟩ := h
  obtain ⟨he, hn, hd⟩ := hX _ hXs
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    simp [handed, hheld]
  have hcode := code_of hp hend wake_svcIn (q := cloneAt pfxM exe) rfl
  have h9' : th.st.st.1.regs.X9.toBitVec = BitVec.ofNat 64 cA := by
    subst h9; show _ = BitVec.ofNat 64 th.st.st.1.regs.X9.toBitVec.toNat; simp
  have h10' : th.st.st.1.regs.X10.toBitVec = BitVec.ofNat 64 meW := by
    subst h10; show _ = BitVec.ofNat 64 th.st.st.1.regs.X10.toBitVec.toNat; simp
  refine ⟨th, tls, cA, meW, hth, hcall, ?_⟩
  rw [← h9', ← h10']
  exact child_at hcode he hn hd (he ▸ hpc) hh htop hlo hsz

end Spike.Lib.A64.Flow.Worker.Wake.Child
