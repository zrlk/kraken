/-
**Main's stack in private memory at the second take's site** (x86-64; the twin of
`Spike/Lib/A64HelloTi2R0.lean`, wake's x86-64 version `Spike/Lib/X64WakeTi2R0.lean`): every aligned word of
main's stack `r0Of` reads at the take site's state, split by where it lies relative to `wc_main`'s region `R`
(base 96 below the stack's top, `hb`, `X64HelloTi2Box`'s), the second `scc_rt_thread_init`'s region
`R' = R.callee (-136) (-248) 8` and the take's `Rt = R'.callee (-48) (-200) 8`:

- off `R`: `StackOff r0 R` (the box's frame condition);
- in `R` off `R'`: `CallerCells R (-136) (-248) 8` (the call's frame);
- in `R'` off `Rt`: `CallerCells R' (-48) (-200) 8` (the take's frame);
- in `Rt`: the take node's cells.

- `stackM_r0H`: `StackM` of `r0Of` from the four.
- `owned_r0H`: `Owned` of `r0Of`.

Wake's `Ti2.addr_ofNat` is reused. No absolute address appears in this file.

## Differences from the AArch64 version

- The base is `v - 96` (`hb`'s `+ 96`, `BoxPureH`'s; A64's `+ 80`); the callee regions are
  `R.callee (-136) (-248) 8` (the call's return slot `-136`) and its `.callee (-48) (-200) 8` (A64's
  `(-144) (-256) 0`, `(-48) (-208) 0`), so `Rt` covers `R`'s offsets `[-384, -176)` and `R'` off `Rt`
  `[-176, -128)` (A64's `[-400, -192)`, `[-192, -144)`); `hRs` is `R.lo ≤ -384 ∧ 8 ≤ R.hi` (A64's `-400`, `0`).
-/
import Spike.Lib.X64HelloTi2Box
import Spike.Lib.X64WakeTi2R0

namespace Spike.Lib.X64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0 (StackM StackOff CallerCells)
open Spike.Lib.X64.WakePh.Ti2 (addr_ofNat)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **Main's stack in private memory** from the four parts (see the module
doc), `R`'s bounds 8-aligned (`h8`), inside `[-384, 8]`'s cover (`hRs`). -/
theorem stackM_r0H (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) (hal : R.base.toNat % 8 = 0)
    (h8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0) (hRs : R.lo ≤ -384 ∧ 8 ≤ R.hi) {m : MachineData}
    (h1 : StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R m) (h2 : CallerCells R (-136) (-248) 8 m)
    (h4 : CallerCells (R.callee (-136) (-248) 8) (-48) (-200) 8 m)
    (h3 : ∀ k, ((R.callee (-136) (-248) 8).callee (-48) (-200) 8).Off k →
      (Mem.loadInt m.dmem (((R.callee (-136) (-248) 8).callee (-48) (-200) 8).addr k) 8).isSome) :
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
  have e136 := addr_boxH (L := L) hb (k := -136) (by omega) (by omega)
  have e184 : (R.callee (-136) (-248) 8).addr (-48) = BitVec.ofNat 64 (R.base.toNat - 184) :=
    addr_ofNat (by rw [show (R.callee (-136) (-248) 8).base = R.addr (-136) from rfl, e136]; omega) (by omega)
  by_cases hin : -176 ≤ (a : Int) - R.base.toNat ∧ (a : Int) - R.base.toNat < -128
  · -- in `R'` off `Rt`
    have h := h4 ((a : Int) - R.base.toNat + 136) ⟨by omega, by show (-248 : Int) ≤ _; omega,
      by show _ + 8 ≤ (8 : Int); omega⟩ (fun ⟨_, _, h⟩ => by simp only [Spike.Lib.Region.callee] at h; omega)
    rwa [show (R.callee (-136) (-248) 8).addr ((a : Int) - R.base.toNat + 136) = BitVec.ofNat 64 a from
      addr_ofNat (by rw [show (R.callee (-136) (-248) 8).base = R.addr (-136) from rfl, e136]; omega) hlt] at h
  by_cases hin3 : -384 ≤ (a : Int) - R.base.toNat ∧ (a : Int) - R.base.toNat < -176
  · -- in `Rt`
    have h := h3 ((a : Int) - R.base.toNat + 184) ⟨by omega, by show (-200 : Int) ≤ _; omega,
      by show _ + 8 ≤ (8 : Int); omega⟩
    rwa [show ((R.callee (-136) (-248) 8).callee (-48) (-200) 8).addr ((a : Int) - R.base.toNat + 184) =
      BitVec.ofNat 64 a from addr_ofNat (by
        rw [show ((R.callee (-136) (-248) 8).callee (-48) (-200) 8).base = (R.callee (-136) (-248) 8).addr (-48)
          from rfl, e184, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hlt] at h
  · -- in `R` off `R'`
    have h := h2 _ hoff (fun ⟨_, h1', h2'⟩ => by simp only [Spike.Lib.Region.callee] at h1' h2'; omega)
    rwa [show R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a from addr_ofNat (by omega) hlt] at h

/-- **Main's stack owned** (`stackM_r0H`), inside the pool. -/
theorem owned_r0H (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) (hal : R.base.toNat % 8 = 0)
    (h8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0) (hRs : R.lo ≤ -384 ∧ 8 ≤ R.hi) {s : State}
    (h1 : StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R s.st.1) (h2 : CallerCells R (-136) (-248) 8 s.st.1)
    (h4 : CallerCells (R.callee (-136) (-248) 8) (-48) (-200) 8 s.st.1)
    (h3 : ∀ k, ((R.callee (-136) (-248) 8).callee (-48) (-200) 8).Off k →
      (Mem.loadInt s.st.1.dmem (((R.callee (-136) (-248) 8).callee (-48) (-200) 8).addr k) 8).isSome) :
    Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s := by
  refine Spike.Lib.X64Consumer.owned_of_stackM ?_ (stackM_r0H hb hal h8 hRs h1 h2 h4 h3)
  show (⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 0#64).toNat, 16384⟩ : Scc.Sem.Range).Sub _
  rw [L.lab_stacks, BitVec.add_zero]
  exact L.stacks_sub

end Spike.Lib.X64.HelloPh.Ti2

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.stackM_r0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.stackM_r0H

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.owned_r0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.owned_r0H
