/-
**The second `scc_rt_thread_init` call's frame facts at the box's base**
(x86-64): `X64WakeTi2Box`'s, `X64WakeTi2Slot`'s, `X64WakeTi2R0`'s and
`X64WakeTi2HatG.pz_fstable_ti2`'s facts restated at the box's region, whose
base is `64` below the first stack's top (`R.base + 64 = stacksA + 16384`,
`%rsp = R.base - 64`; `X64WakeBox`, `X64WakeBoxW`, `X64WakeHMid.BoxPure`,
`CloneP`), with the thread init's callee region `R.callee (-72) (-248) 8`
(`HMidP.ti`, `wake_wc_mid_hatW`'s `hti`). That callee region is the one the
`+ 56` forms name `R.callee (-80) (-248) 8` at a base `8` higher.

- `addr_box64`: `R`'s addresses in `[-320, 64]` without wrap;
- `bandP_box64`: `BandP L R (-320)`;
- `hout_box64`, `hRS_box64`: `r1Of` off the callee's region;
- `pz_fstable_ti2_64`: `Pz r1Of` kept by the callee region's frames;
- `slotP_keep64`: main's slots `-16`, `-8` kept by the callee's frame;
- `stackM_r0_64`, `owned_r0_64`: main's stack in private memory, owned.

x86-64 only (A64 has one geometry, `+ 48`). These are new statements; the
`+ 56` forms (`addr_box`, `bandP_box`, `hout_box`, `hRS_box`,
`pz_fstable_ti2`, `slotP_keep`, `stackM_r0`, `owned_r0`) are unchanged.

**Unlike the `+ 56` forms**: the band is `[-320, 8]` (A64-style `[lo, 8]`;
the frames reach `-72 - 248`); the callee is at `-72` (`+ 56`: `-80`), so
the take's region `R'.callee (-48) (-200) 8` covers `R`'s offsets
`[-320, -112)` and `R'` off it `[-112, -64)`; `stackM_r0_64` and
`owned_r0_64` take no `hRs`; `slotP_keep64` takes the call's abstract state at
any static offsets `o` (`+ 56`: `oW`).

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeTi2Slot
import Spike.Lib.X64WakeTi2R0
import Spike.Lib.X64WakeTi2HatG

namespace Spike.Lib.X64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0 (StackM StackOff CallerCells)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **`R`'s addresses in `[-320, 64]`** are `base + k`, without wrap. -/
theorem addr_box64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) {k : Int} (h1 : -320 ≤ k) (h2 : k ≤ 64) :
    ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have hf := L.pool_fit
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The frames `[-320, 8]` around `wc_main`'s base are on the pool**: in
the first stack, below its top. -/
theorem bandP_box64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) : BandP L R (-320) := by
  intro k h1 h2
  have ha := addr_box64 hb h1 (by omega)
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨s1, s2⟩ := hs
  omega

/-- **The second stack is above the callee's region** `R.callee (-72) (-248) 8`
(word by word, `threadInit_segWAt`'s `hout`). -/
theorem hout_box64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) :
    ∀ a, a % 8 = 0 → (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).contains a →
      (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-72) (-248) 8).base.toNat + (R.callee (-72) (-248) 8).lo ∨
        ((R.callee (-72) (-248) 8).base.toNat : Int) + (R.callee (-72) (-248) 8).hi ≤ a := by
  intro a _ ha _
  have hc := addr_box64 hb (k := -72) (by decide) (by decide)
  have hl := r1_lo (L := L)
  simp only [Scc.Sem.Range.contains] at ha
  refine .inr ?_
  show ((R.addr (-72)).toNat : Int) + 8 ≤ a
  omega

/-- **The callee's region's cells are off the second stack**
(`threadInit_segWAt`'s `hRS`). -/
theorem hRS_box64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) :
    ∀ k, (R.callee (-72) (-248) 8).Off k → ∀ j < 8,
      (R.callee (-72) (-248) 8).addr k + BitVec.ofNat 64 j ∉
        Scc.Sem.Kernel.addrs (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) := by
  intro k hk j hj hm
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  have hx := List.mem_range.mp hx
  obtain ⟨-, h3, h4⟩ := hk
  simp only [Spike.Lib.Region.callee] at h3 h4
  rw [Spike.Lib.Region.callee_addr] at he
  have ha := addr_box64 hb (k := -72 + k) (by omega) (by omega)
  have hl := r1_lo (L := L)
  have hf := L.pool_fit
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  obtain ⟨s1, s2⟩ := hs
  have hsz : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).size = 16384 := rfl
  have h1 := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)] at h1
  have hlt : (R.addr (-72 + k)).toNat + j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt] at h1
  rw [hsz] at hx
  have hlt2 : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).lo + x < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h1
  omega

/-- **`Pz r1Of` is kept by the thread init's region's frames**: the region
`R.callee (-72) (-248) 8` has its top `64` below `R`'s base, itself `64`
below `r1Of` (`hbase`). -/
theorem pz_fstable_ti2_64 (hbase : R.base.toNat + 64 = L.stacksA.toNat + 16384) :
    Spike.Lib.X64.FStable (R.callee (-72) (-248) 8)
      (Spike.Lib.X64Consumer.Pz (Spike.Lib.X64.Rt.PreChild.r1Of L.lab)) := by
  have hst := L.stacks_sub
  have hpf := L.pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hr1 := r1_lo (L := L)
  have hx := R.base.isLt
  have hb : (R.callee (-72) (-248) 8).base.toNat = R.base.toNat - 72 := by
    show (R.base + BitVec.ofInt 64 (-72)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofInt]
    have : ((-(72 : Int)) % (2 ^ 64 : Nat) : Int).toNat = 2 ^ 64 - 72 := by omega
    rw [this]; omega
  refine Spike.Lib.X64.WakePh.Pz.pz_fstable (Spike.Lib.X64.WakePh.Pz.r1Of_fit L) ?_
  rw [hb, hr1]; show ((R.base.toNat - 72 : Nat) : Int) + 8 ≤ _; omega

/-- **`SlotP` at every state the callee's frame keeps**: at the call the
slots hold `cA` and `mw` (`hFm`: an abstract state of `R` whose cells off
the callee's region `R.callee (-72) (-248) 8` the frame keeps), `cA` the
box's `b` and `mw` main's `t0`; the slots off the callee's region by the
box's base (`hb`), inside `R` (`hRs`). -/
theorem slotP_keep64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -16 ∧ 0 ≤ R.hi)
    {b t0 : Nat} {cA mw : BitVec 64} (hcA : cA.toNat = b) (hm : mw.toNat = t0) {F' : MachineData → Prop}
    {o : Spike.Lib.X64.SO}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.X64.Abs R o mC σC ∧ σC.slot (-16) = cA ∧
      σC.slot (-8) = mw ∧ ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.X64.DFrame (R.callee (-72) (-248) 8) m m' → SlotP R b t0 m' := by
  intro m m' hm0 hd
  obtain ⟨mC, σC, hA, h16, h8, hk⟩ := hFm m hm0
  have hB := R.base.isLt
  have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have o8 : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have n16 : ¬ (R.callee (-72) (-248) 8).Off (-16 - -72) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have n8 : ¬ (R.callee (-72) (-248) 8).Off (-8 - -72) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have a16 := addr_box64 (L := L) hb (k := -16) (by omega) (by omega)
  have a8 := addr_box64 (L := L) hb (k := -8) (by omega) (by omega)
  have a72 := addr_box64 (L := L) hb (k := -72) (by omega) (by omega)
  have d16 : Mem.loadInt m'.dmem (R.addr (-16)) 8 = Mem.loadInt m.dmem (R.addr (-16)) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-72)).toNat : Int) + 8 ≤ ((R.addr (-16)).toNat : Int); omega))
  have d8 : Mem.loadInt m'.dmem (R.addr (-8)) 8 = Mem.loadInt m.dmem (R.addr (-8)) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-72)).toNat : Int) + 8 ≤ ((R.addr (-8)).toNat : Int); omega))
  obtain ⟨j16, e16, v16⟩ := hA.slot _ o16
  obtain ⟨j8, e8, v8⟩ := hA.slot _ o8
  refine ⟨j16, j8, by rw [d16, hk _ o16 n16, e16], by rw [v16, h16, hcA], by rw [d8, hk _ o8 n8, e8],
    by rw [v8, h8, hm]⟩

/-- **Main's stack in private memory** from the four parts (`stackM_r0`'s,
the callee at `-72`), `R`'s bounds 8-aligned (`h8`); no bound on `R`
(`stackM_r0`'s `hRs`) is needed. -/
theorem stackM_r0_64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) (hal : R.base.toNat % 8 = 0)
    (h8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0) {m : MachineData}
    (h1 : StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R m) (h2 : CallerCells R (-72) (-248) 8 m)
    (h4 : CallerCells (R.callee (-72) (-248) 8) (-48) (-200) 8 m)
    (h3 : ∀ k, ((R.callee (-72) (-248) 8).callee (-48) (-200) 8).Off k →
      (Mem.loadInt m.dmem (((R.callee (-72) (-248) 8).callee (-48) (-200) 8).addr k) 8).isSome) :
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
  have e72 := addr_box64 (L := L) hb (k := -72) (by omega) (by omega)
  have e120 : (R.callee (-72) (-248) 8).addr (-48) = BitVec.ofNat 64 (R.base.toNat - 120) :=
    addr_ofNat (by rw [show (R.callee (-72) (-248) 8).base = R.addr (-72) from rfl, e72]; omega) (by omega)
  by_cases hin : -112 ≤ (a : Int) - R.base.toNat ∧ (a : Int) - R.base.toNat < -64
  · -- in `R'` off `Rt`
    have h := h4 ((a : Int) - R.base.toNat + 72) ⟨by omega, by show (-248 : Int) ≤ _; omega,
      by show _ + 8 ≤ (8 : Int); omega⟩ (fun ⟨_, _, h⟩ => by simp only [Spike.Lib.Region.callee] at h; omega)
    rwa [show (R.callee (-72) (-248) 8).addr ((a : Int) - R.base.toNat + 72) = BitVec.ofNat 64 a from
      addr_ofNat (by rw [show (R.callee (-72) (-248) 8).base = R.addr (-72) from rfl, e72]; omega) hlt] at h
  by_cases hin3 : -320 ≤ (a : Int) - R.base.toNat ∧ (a : Int) - R.base.toNat < -112
  · -- in `Rt`
    have h := h3 ((a : Int) - R.base.toNat + 120) ⟨by omega, by show (-200 : Int) ≤ _; omega,
      by show _ + 8 ≤ (8 : Int); omega⟩
    rwa [show ((R.callee (-72) (-248) 8).callee (-48) (-200) 8).addr ((a : Int) - R.base.toNat + 120) =
      BitVec.ofNat 64 a from addr_ofNat (by
        rw [show ((R.callee (-72) (-248) 8).callee (-48) (-200) 8).base = (R.callee (-72) (-248) 8).addr (-48)
          from rfl, e120, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hlt] at h
  · -- in `R` off `R'`
    have h := h2 _ hoff (fun ⟨_, h1', h2'⟩ => by simp only [Spike.Lib.Region.callee] at h1' h2'; omega)
    rwa [show R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a from addr_ofNat (by omega) hlt] at h

/-- **Main's stack owned** (`stackM_r0_64`), inside the pool. -/
theorem owned_r0_64 (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384) (hal : R.base.toNat % 8 = 0)
    (h8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0) {s : State}
    (h1 : StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R s.st.1) (h2 : CallerCells R (-72) (-248) 8 s.st.1)
    (h4 : CallerCells (R.callee (-72) (-248) 8) (-48) (-200) 8 s.st.1)
    (h3 : ∀ k, ((R.callee (-72) (-248) 8).callee (-48) (-200) 8).Off k →
      (Mem.loadInt s.st.1.dmem (((R.callee (-72) (-248) 8).callee (-48) (-200) 8).addr k) 8).isSome) :
    Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s := by
  refine Spike.Lib.X64Consumer.owned_of_stackM ?_ (stackM_r0_64 hb hal h8 h1 h2 h4 h3)
  show (⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 0#64).toNat, 16384⟩ : Scc.Sem.Range).Sub _
  rw [L.lab_stacks, BitVec.add_zero]
  exact L.stacks_sub

end Spike.Lib.X64.WakePh.Ti2

/-- info: 'Spike.Lib.X64.WakePh.Ti2.addr_box64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.addr_box64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.bandP_box64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.bandP_box64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.hout_box64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.hout_box64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.hRS_box64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.hRS_box64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.pz_fstable_ti2_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.pz_fstable_ti2_64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.slotP_keep64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.slotP_keep64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.stackM_r0_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.stackM_r0_64

/-- info: 'Spike.Lib.X64.WakePh.Ti2.owned_r0_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.owned_r0_64
