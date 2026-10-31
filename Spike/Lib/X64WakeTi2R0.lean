/-
**Main's stack in private memory at the second take's site** (x86-64; twin
of `Spike/Lib/A64WakeTi2R0.lean`, `hti_W`'s `X0T`): every aligned word of
main's stack `r0Of` reads at the take site's state, split by where it lies
relative to `wc_main`'s region `R` (base 56 below the stack's top, `hb`),
the second `scc_rt_thread_init`'s region `R' = R.callee (-80) (-248) 8` and
the take's `Rt = R'.callee (-48) (-200) 8`:

- off `R`: `StackOff r0 R` (the box's frame condition);
- in `R` off `R'`: `CallerCells R (-80) (-248) 8` (the call's frame);
- in `R'` off `Rt`: `CallerCells R' (-48) (-200) 8` (the take's frame);
- in `Rt`: the take node's cells.

- `addr_ofNat`: an address without wrap as `ofNat`.
- `stackM_r0`: `StackM` of `r0Of` from the four.
- `owned_r0`: `Owned` of `r0Of`.

**Unlike AArch64**: the base is `v - 56` (`hb`'s `+ 56`, A64's `+ 48`); the
callee regions are `R.callee (-80) (-248) 8` and its `.callee (-48) (-200)
8` (A64's `(-80) (-256) 0`, `(-48) (-208) 0`), so `Rt` covers `R`'s
offsets `[-328, -120)` and `R'` off `Rt` `[-120, -72)` (A64's `[-336,
-128)`, `[-128, -80)`); `hRs` is `R.lo ≤ -328 ∧ 8 ≤ R.hi` (A64's `-336`,
`0`).

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeTi2Box
import Spike.Lib.X64OwnedStackM
import Spike.Lib.Rt.X64RtTi2

namespace Spike.Lib.X64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0 (StackM StackOff CallerCells)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **An address without wrap is `ofNat`**: `base + k` at `a`. -/
theorem addr_ofNat {base : BitVec 64} {k : Int} {a : Nat} (h : (base.toNat : Int) + k = a) (ha : a < 2 ^ 64) :
    base + BitVec.ofInt 64 k = BitVec.ofNat 64 a := by
  rw [show base + BitVec.ofInt 64 k = BitVec.ofInt 64 ((base.toNat : Int) + k) by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq], h]
  rfl

/-- **Main's stack in private memory** from the four parts (see the module
doc), `R`'s bounds 8-aligned (`h8`), inside `[-328, 8]`'s cover (`hRs`). -/
theorem stackM_r0 (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) (hal : R.base.toNat % 8 = 0)
    (h8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0) (hRs : R.lo ≤ -328 ∧ 8 ≤ R.hi) {m : MachineData}
    (h1 : StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R m) (h2 : CallerCells R (-80) (-248) 8 m)
    (h4 : CallerCells (R.callee (-80) (-248) 8) (-48) (-200) 8 m)
    (h3 : ∀ k, ((R.callee (-80) (-248) 8).callee (-48) (-200) 8).Off k →
      (Mem.loadInt m.dmem (((R.callee (-80) (-248) 8).callee (-48) (-200) 8).addr k) 8).isSome) :
    StackM (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) m := by
  intro a ha8 ha ha7
  have hr0 : (Spike.Lib.X64.Rt.Ti2.r0Of L.lab).lo = L.stacksA.toNat := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 0#64).toNat = _
    rw [L.lab_stacks, BitVec.add_zero]
  have hsz : (Spike.Lib.X64.Rt.Ti2.r0Of L.lab).size = 16384 := rfl
  simp only [Scc.Sem.Range.contains, hr0, hsz] at ha ha7
  have hB := R.base.isLt
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact h1 a ha8 (by simp only [Scc.Sem.Range.contains, hr0, hsz]; omega)
      (by simp only [Scc.Sem.Range.contains, hr0, hsz]; omega) hout
  have hlt : a < 2 ^ 64 := by
    have := L.pool_fit
    obtain ⟨h1', h2'⟩ := L.stacks_sub
    simp only at h1' h2'
    omega
  have hoff : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
  have e80 := addr_box (L := L) hb (k := -80) (by omega) (by omega)
  have e128 : (R.callee (-80) (-248) 8).addr (-48) = BitVec.ofNat 64 (R.base.toNat - 128) :=
    addr_ofNat (by rw [show (R.callee (-80) (-248) 8).base = R.addr (-80) from rfl, e80]; omega) (by omega)
  by_cases hin : -120 ≤ (a : Int) - R.base.toNat ∧ (a : Int) - R.base.toNat < -72
  · -- in `R'` off `Rt`
    have h := h4 ((a : Int) - R.base.toNat + 80) ⟨by omega, by show (-248 : Int) ≤ _; omega,
      by show _ + 8 ≤ (8 : Int); omega⟩ (fun ⟨_, _, h⟩ => by simp only [Spike.Lib.Region.callee] at h; omega)
    rwa [show (R.callee (-80) (-248) 8).addr ((a : Int) - R.base.toNat + 80) = BitVec.ofNat 64 a from
      addr_ofNat (by rw [show (R.callee (-80) (-248) 8).base = R.addr (-80) from rfl, e80]; omega) hlt] at h
  by_cases hin3 : -328 ≤ (a : Int) - R.base.toNat ∧ (a : Int) - R.base.toNat < -120
  · -- in `Rt`
    have h := h3 ((a : Int) - R.base.toNat + 128) ⟨by omega, by show (-200 : Int) ≤ _; omega,
      by show _ + 8 ≤ (8 : Int); omega⟩
    rwa [show ((R.callee (-80) (-248) 8).callee (-48) (-200) 8).addr ((a : Int) - R.base.toNat + 128) =
      BitVec.ofNat 64 a from addr_ofNat (by
        rw [show ((R.callee (-80) (-248) 8).callee (-48) (-200) 8).base = (R.callee (-80) (-248) 8).addr (-48)
          from rfl, e128, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hlt] at h
  · -- in `R` off `R'`
    have h := h2 _ hoff (fun ⟨_, h1', h2'⟩ => by simp only [Spike.Lib.Region.callee] at h1' h2'; omega)
    rwa [show R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a from addr_ofNat (by omega) hlt] at h

/-- **Main's stack owned** (`stackM_r0`), inside the pool. -/
theorem owned_r0 (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) (hal : R.base.toNat % 8 = 0)
    (h8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0) (hRs : R.lo ≤ -328 ∧ 8 ≤ R.hi) {s : State}
    (h1 : StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R s.st.1) (h2 : CallerCells R (-80) (-248) 8 s.st.1)
    (h4 : CallerCells (R.callee (-80) (-248) 8) (-48) (-200) 8 s.st.1)
    (h3 : ∀ k, ((R.callee (-80) (-248) 8).callee (-48) (-200) 8).Off k →
      (Mem.loadInt s.st.1.dmem (((R.callee (-80) (-248) 8).callee (-48) (-200) 8).addr k) 8).isSome) :
    Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s := by
  refine Spike.Lib.X64Consumer.owned_of_stackM ?_ (stackM_r0 hb hal h8 hRs h1 h2 h4 h3)
  show (⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 0#64).toNat, 16384⟩ : Scc.Sem.Range).Sub _
  rw [L.lab_stacks, BitVec.add_zero]
  exact L.stacks_sub

end Spike.Lib.X64.WakePh.Ti2

/-- info: 'Spike.Lib.X64.WakePh.Ti2.addr_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.addr_ofNat

/-- info: 'Spike.Lib.X64.WakePh.Ti2.stackM_r0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.stackM_r0

/-- info: 'Spike.Lib.X64.WakePh.Ti2.owned_r0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.owned_r0
