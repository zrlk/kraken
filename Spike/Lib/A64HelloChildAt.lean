/-
**hello.w on AArch64: the child after the `clone` is at the stub's node**
(the spawn's child half; wake's `A64WakeChildAt`): the thread
`childAfter` gives (`Spike.Lib.Handover.childAfter`, the handed range `r1`
copied into its empty private memory) is in the fragment `At … (childN …)`
of `Spike.Lib.A64.Flow.Worker.Hello.Child`, so `seg_childStub` runs it.

The region is wake's `childR` (the handed stack's top, offsets `[lo, 0)`);
every word of it is mapped (`Wake.Child.loadInt_copyRange`), and the frame
condition is the child's first memory outside the region (`DFrame`). The
worker's six words are the parent's `x9 .. x14` (the slice's four words,
the cell, main's word), the thread pointer `tls`, `sp` the top.

- `child_atH`: the child after a `clone` (at any pc `q` holding the `svc`)
  whose stack range is handed is at `childN`.
- `clonePreH_child_at`: from main's state at its `clone` (`ClonePreH`) in a
  layout of `helloProg`, the child is at `childN` with the words
  `sl0 .. sl3`, `cA`, `meW`, the thread pointer `tls`, `sp` the top of `r1`.

Deferred (B4c/B8): the composition with `seg_childStub` and the spawn's
`hCl` obligation.
-/
import Spike.Lib.A64HelloChild
import Spike.Lib.A64WakeChildAt
import Spike.Lib.A64HelloWcSp6
import Spike.Lib.A64HelloClonePreH

namespace Spike.Lib.A64.Flow.Worker.Hello.Child

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (svcB childR loadInt_copyRange)
open Spike.Lib.HelloPreA (cloneAtH ClonePreH)
open SccCode (helloProg)

/-- The clone's `svc` in hello's program, 25 instructions past `.sp6`. -/
theorem hello_svcIn : blockAt helloProg (pfxM ++ ".sp6") 25 svcB = true := by
  have h := Spike.Lib.A64.HelloPh.WcSp6.hello_wcSp6In
  simp only [Spike.Lib.A64.HelloPh.WcSp6.wcSp6In, Bool.and_eq_true] at h
  exact h.2

/-- **The child after the `clone` is at the stub's node**: a thread `t` at
the clone's `svc` (pc `q`, a 4-byte cell there: `hcode`; `childN`'s pc is
`q + 4`: `hq`), whose stack top `r1.lo + r1.size` ends the handed range
`r1`, gives a child in `At` of `childN` for the region `childR` (no deeper
than `r1`), the frame condition its first memory outside the region, the
worker's words the parent's `x9 .. x14`, the thread pointer `tls`, `sp` the
top, any source control `cW`. -/
theorem child_atH {pfx : String} {exe : _root_.Executable} {endPc : Int64} {q : Int64} {x : KState}
    {tid : Nat} {t : Thread isaLSE2} {r1 : Range} {tls : Nat} {lo : Int} {cW : Ctl}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q svcB)
    (hq : (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25) = q)
    (he : t.st.exe = exe) (hn : t.st.endPc = endPc) (hd : t.st.decls = {})
    (hpc : t.st.st.2 = q)
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (htop : r1.lo + r1.size < 2 ^ 64) (_hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) :
    At exe endPc (childR (r1.lo + r1.size) lo)
      (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1)
      (childN pfx (_root_.Executable.labels exe).label cW
        ⟨t.st.st.1.regs.X9.toBitVec, t.st.st.1.regs.X10.toBitVec, t.st.st.1.regs.X11.toBitVec,
          t.st.st.1.regs.X12.toBitVec, t.st.st.1.regs.X13.toBitVec, t.st.st.1.regs.X14.toBitVec⟩
        (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
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
    rw [hnext, hpc, ← hq]; rfl
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
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The child after main's `clone` is at the stub's node** (hello's
layout `hp`): main's state at the clone (`ClonePreH`; `hX`: its runtime
facts pin the executable, its end and no declarations) gives the child,
after the clone hands it `r1`, in `At` of `childN` for `childR` (no deeper
than `r1`), the words `ClonePreH`'s `sl0 .. sl3`, `cA`, `meW`, the thread
pointer its `tls`. -/
theorem clonePreH_child_at {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) {lo : Int} (hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) (cW : Ctl) :
    ∃ (th : Thread isaLSE2) (tls sl0 sl1 sl2 sl3 cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
      At exe endPc (childR (r1.lo + r1.size) lo)
        (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
        (childN pfxM (_root_.Executable.labels exe).label cW
          ⟨BitVec.ofNat 64 sl0, BitVec.ofNat 64 sl1, BitVec.ofNat 64 sl2, BitVec.ofNat 64 sl3,
            BitVec.ofNat 64 cA, BitVec.ofNat 64 meW⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
        (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st cW := by
  obtain ⟨th, -, -, tls, cA, meW, sl0, sl1, sl2, sl3, -, -, hth, -, hpc, -, -, hcall, -, -,
    h9, h10, h11, h12, h13, h14, hheld, -, -, -, hXs, -⟩ := h
  obtain ⟨he, hn, hd⟩ := hX _ hXs
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    simp [handed, hheld]
  have hcode := code_of hp hend hello_svcIn (q := cloneAtH pfxM exe) rfl
  have hw : ∀ {v : BitVec 64} {n : Nat}, v.toNat = n → v = BitVec.ofNat 64 n := by
    intro v n hv; subst hv; simp
  refine ⟨th, tls, sl0, sl1, sl2, sl3, cA, meW, hth, hcall, ?_⟩
  rw [← hw h9, ← hw h10, ← hw h11, ← hw h12, ← hw h13, ← hw h14]
  exact child_atH hcode rfl he hn hd (he ▸ hpc) hh htop hlo hsz

end Spike.Lib.A64.Flow.Worker.Hello.Child

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.clonePreH_child_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.clonePreH_child_at
