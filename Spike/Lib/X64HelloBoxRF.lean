/-
**hello.w on x86-64: the box's region and frame-condition facts** (the twin of
`Spike.Lib.A64HelloBoxRF`). These are the twins of wake's
`X64WakeTakeFLy.wF_takeMem`/`stackOff_r0_box` and `X64WakeBoxW.fS_dmem`/`wF_dmem`,
taken at hello's `wc_main` frame condition at the call,
`wcF (RS Lsw v) D (FS Ly rS0 Lsw 0 v) m1 σ1`, with the runtime's words unmapped
under it. These are `H1GAHG`'s region and frame fields at the box's real ghost
(`RootHP.hP_ofG`).

- `rtF_of_wn`: `WordsNoneP` gives `rtF`: every runtime word's bytes are in
  `.data` or `pinned` (`words_mapped`).
- `unF_of_wn`: `WordsNoneP` gives the second TCB's words unmapped (`tH = pinA +
  112`, six words), given that the pinned region reaches `pinA + 200` (`hpin2`).
- `wcF_dmemH`: the frame condition reads memory only (`fcg`).
- `wcF_takeMemH`: the frame condition survives the child's stack take (`fcl`).
- `stackOff_r0_boxH`: main's stack is mapped off `wc_main`'s region under the
  frame condition (`hF0`), at the box's region `(wcR (RS Lsw v) D).fp (-8)`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The region is `scc_rt_main`'s, `MainGlue.RS Lsw v = (swR v (-Lsw) 0).callee (-8) (8 - Lsw) 8`, because
  `call scc_rt_main` pushes the return address at `v - 8`. The same holds for x86-64 wake (`X64WakeTakeFLy`) and
  for `X64HelloRootHPD.GJ1RH`. AArch64 uses `swR v (-helloLsw) 0`. `wcR R D = R.callee (-80) (-D) 8`
  (`X64HelloMain`). `FS` also carries the switch region's `CallerCells`, which the take keeps like the other words
  below `v`. The limit word is `limA (tpOf (tcbS Ly))`.
- **The depths are parameters** (`Lsw`, `D`). AArch64 fixes `helloLsw`/`helloD`. x86-64's are
  `X64HelloFrameD`'s `helloLsw = 488`, `helloD = 400`, which `GJ1RH` pins. `wcF_takeMemH` takes
  `8 ≤ Lsw ≤ 16384`. `stackOff_r0_boxH` takes `8 ≤ D`, `88 + D ≤ Lsw ≤ 16384` (`helloD_fit`) and `Lsw % 8 = 0`.
  Every word of `scc_rt_main`'s region off `wc_main`'s is kept from the call (`CKept`, `Abs`), so the proof needs
  no equality between the depths.
- `stackOff_r0_boxH`'s region is the box's frame based at the saved `%rbp`, `(wcR (RS Lsw v) D).fp (-8)`
  (`GJ1RH`'s `R`, where `bXH` is stated; base `v - 96`), not `wcR (RS Lsw v) D`: the same cells
  (`Region.fp_out'`). AArch64's `bXH` is on `wcR` itself.
- The layout is `RuntimeLayout.ofPlaceWX`, and `a13data` is `Scc.Cert.Spawn.X64`'s.
-/
import Spike.Lib.X64HelloBox
import Spike.Lib.X64WakeTakeFLy
import Spike.Lib.X64HelloMain
import Spike.Lib.X64HelloWcSp3

namespace Spike.Lib.X64.HelloPh.BoxRF

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.Flow.Ret0 (takeMem)
open Spike.Lib.X64.Flow.HelloM (wcR wcF)
open Spike.Lib.X64.WakePh.MainGlue (FS RS)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib.PlaceWX

/-! ## The runtime's words under `WordsNoneP` -/

/-- **`WordsNoneP` gives `rtF`**: each runtime word's bytes lie in `.data` or `pinned` (`words_mapped`), both
private. -/
theorem rtF_of_wn (L : RuntimeLayout) {m : MachineData} (h : WordsNoneP L.Λ m.dmem) : Spike.Lib.X64.Rt.rtF L m :=
  fun a ha => h a fun j hj => ((L.words_mapped a ha).2.2 j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

/-- **`WordsNoneP` gives the second TCB's words unmapped** (`H1GAHG.hunF`): `tH = pinA + 144` and its six words lie
in `[pinA + 144, pinA + 192)`, inside the pinned region (`pinA` its base, `hpin2` its reach). -/
theorem unF_of_wn (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {m : MachineData}
    (h : WordsNoneP (Ly).Λ m.dmem) :
    ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (Spike.Lib.X64.Flow.HelloWc.tH (Ly).lab), Mem.loadInt m.dmem a 8 = none := by
  have hp0 : (Ly).pinA.toNat = (Ly).Λ.pinned.lo := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hpw i
  have hs := (Ly).words_small _ (Ly).pin_mem
  have hT : (Spike.Lib.X64.Flow.HelloWc.tH (Ly).lab).toNat = (Ly).pinA.toNat + 144 := by
    show (Spike.Lib.X64.Flow.Ret0.pinA (_root_.Executable.labels (Ly).exe).label + 144#64).toNat = _
    rw [(Ly).lab_pin, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  intro a ha
  apply h
  have hk : ∃ k < 6, a = Spike.Lib.X64.Flow.HelloWc.tH (Ly).lab + BitVec.ofNat 64 (8 * k) := by
    simp only [Spike.Lib.X64.Rt.Ti.tiAddrs, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with h | h | h | h | h | h <;> exact ⟨_, by decide, h⟩
  obtain ⟨k, hk, rfl⟩ := hk
  intro j hj
  have ha : (Spike.Lib.X64.Flow.HelloWc.tH (Ly).lab + BitVec.ofNat 64 (8 * k)).toNat =
      (Ly).pinA.toNat + 144 + 8 * k := by
    rw [BitVec.toNat_add, hT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [ha]
  unfold Spike.Lib.X64.DmemPriv.PrivB Scc.Sem.Range.contains
  omega

/-! ## `wc_main`'s frame condition at the call -/

/-- **The frame condition reads memory only** (`H1GAHG.fcg`; wake's `X64WakeBoxW.fS_dmem`/`wF_dmem`). -/
theorem wcF_dmemH {R : Spike.Lib.Region} {D : Int} {L : RuntimeLayout} {rS : Scc.Sem.Range} {Lsw : Int}
    {k0 v : BitVec 64} {m1 : MachineData} {σ1 : Spike.Lib.X64.AS} :
    ∀ m m' : MachineData, m'.dmem = m.dmem → wcF R D (FS L rS Lsw k0 v) m1 σ1 m → wcF R D (FS L rS Lsw k0 v) m1 σ1 m' :=
  fun _ _ e h => ⟨by
      simpa only [Spike.Lib.X64.WakePh.MainGlue.FS, Spike.Lib.X64.Rt.swFSL, Spike.Lib.X64.Flow.Ret0.swF,
        Spike.Lib.X64.Flow.Ret0.StackOff, Spike.Lib.X64.Flow.Ret0.CallerCells, e] using h.1,
    fun k hk hn => by rw [e]; exact h.2.1 k hk hn, h.2.2⟩

/-- The pool reaches the second stack's end (A13's data part). -/
private theorem pool_32H (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    (Ly).stacksA.toNat + 32768 ≤ (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size := by
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
  exact hA13.2

/-- **A word below `stacksA + 16384` is off the child's stack.** -/
private theorem below_offH (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a.toNat + 8 ≤ (Ly).stacksA.toNat + 16384) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (R1) := by
  intro j hj hm
  have hlo := Spike.Lib.X64.WakePh.Ti2.r1_lo (L := Ly)
  have h32 := pool_32H hpw i hA13
  have hf := (Ly).pool_fit
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  have hk := List.mem_range.mp hk
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [hlo] at this
  simp only [Spike.Lib.X64.Rt.PreChild.r1Of] at hk
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **A runtime word is off the child's stack**: it is clear of the pool (`words_pool`), the child's stack inside
it (`hsub1_W`). -/
private theorem rt_offH (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a ∈ (Ly).rtWords) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (R1) := by
  intro j hj hm
  have hsub := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hpw i hA13
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  have hk := List.mem_range.mp hk
  have hs := (Ly).words_small a ha
  have hp := (Ly).words_pool a ha
  have hf := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := hsub
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  simp only [Spike.Lib.X64WakeOSide.r1W] at h1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  unfold Spike.Lib.X64.Rt.Clear at hp
  omega

omit hpw i in
/-- `scc_rt_main`'s region `RS Lsw v` at a base `v` high enough does not wrap, and its base is `v - 8`. -/
private theorem rs_okH {Lsw : Int} {v : BitVec 64} (hL8 : 8 ≤ Lsw) (hv : Lsw ≤ v.toNat) :
    (RS Lsw v).OK ∧ ((RS Lsw v).base.toNat : Int) = v.toNat + -8 := by
  have hvl := v.isLt
  have hR : (swR v (-Lsw) 0).OK :=
    ⟨by show (0 : Int) ≤ v.toNat + -Lsw; omega, by show (v.toNat : Int) + 0 ≤ 2 ^ 64; omega⟩
  exact ⟨Spike.Lib.Region.callee_ok hR (by show -Lsw ≤ -8 - 0 + (8 - Lsw); omega)
      (by show 8 - Lsw ≤ 0; omega) (by show (-8 - 0 : Int) < 0; decide) (by show (-8 - 0 + 8 : Int) ≤ 0; decide),
    Spike.Lib.Region.callee_base hR (by show -Lsw ≤ -8 - 0 + (8 - Lsw); omega) (by show 8 - Lsw ≤ 0; omega)
      (by show (-8 - 0 : Int) < 0; decide)⟩

/-- **The frame condition survives the child's stack take** (`H1GAHG.fcl`; wake's `X64WakeTakeFLy.wF_takeMem` at a
depth `Lsw`): `WordsNoneP` by `wordsNoneP_takeMem`; the limit word a runtime word; stack 0's words, the switch
region's cells and `wc_main`'s cells below `v = stacksA + 16384`, all off the child's stack. -/
theorem wcF_takeMemH (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {Lsw D : Int} (hL8 : 8 ≤ Lsw) (hL : Lsw ≤ 16384) {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} :
    ∀ m (pm : _root_.Mem 64),
      wcF (RS Lsw v) D (FS (Ly) (RS0) Lsw 0#64 v) m0 σC m →
      wcF (RS Lsw v) D (FS (Ly) (RS0) Lsw 0#64 v) m0 σC (takeMem pm (R1) m) := by
  intro m pm ⟨⟨⟨hwn, ⟨hv, hlim⟩, hso⟩, hcc⟩, hck, hA⟩
  have hsub := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hpw i hA13
  have hvS := Spike.Lib.X64.WakePh.StartPlaceLy.v_top hpw i hv
  have hf := (Ly).pool_fit
  have hst := (Ly).stacks_sub
  simp only [Scc.Sem.Range.Sub] at hst
  refine ⟨⟨⟨Spike.Lib.X64.Rt.wordsNoneP_takeMem (PlaceWX.wf_link_of_placeWX i hpw) hsub hwn, ⟨hv, ?_⟩, ?_⟩,
    ?_⟩, ?_, hA⟩
  · -- the limit word: a runtime word
    have hw : Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf
        (Spike.Lib.X64.WakePh.MainGlue.tcbS (Ly))) ∈ (Ly).rtWords := by
      show Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (Spike.Lib.X64.Flow.Ret0.pinA
        (_root_.Executable.labels (Ly).exe).label + 0#64 + 8#64)) ∈ _
      rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
      exact (Ly).fld_mem (i := 1) (by decide)
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (rt_offH hpw i hA13 hw)]
    exact hlim
  · -- stack 0's words: below `stacksA + 16384`
    intro a h8 ha ha7 hout
    have ha7' := ha7
    simp only [Scc.Sem.Range.contains, BitVec.add_zero] at ha7'
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (below_offH hpw i hA13 (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))]
    exact hso a h8 ha ha7 hout
  · -- the switch region's cells: below `v`
    intro k hk hn
    have hvl := v.isLt
    have hR : (swR v (-Lsw) 0).OK :=
      ⟨by show (0 : Int) ≤ v.toNat + -Lsw; omega, by show (v.toNat : Int) + 0 ≤ 2 ^ 64; omega⟩
    have he := (swR v (-Lsw) 0).addr_toNat hR hk
    have hk2 : k + 8 ≤ 0 := hk.2.2
    simp only [show (swR v (-Lsw) 0).base = v from rfl] at he
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (below_offH hpw i hA13 (by omega))]
    exact hcc k hk hn
  · -- `wc_main`'s cells: below `v`
    intro k hk hn
    obtain ⟨hR, hb⟩ := rs_okH hL8 (v := v) (by omega)
    have he := (RS Lsw v).addr_toNat hR hk
    have hk2 : k + 8 ≤ 8 := hk.2.2
    rw [hb] at he
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (below_offH hpw i hA13 (by omega))]
    exact hck k hk hn

/-- **Main's stack mapped off `wc_main`'s region** (`H1GAHG.hF0`; wake's `X64WakeTakeFLy.stackOff_r0_box` at depths
`Lsw`/`D`), at the box's frame based at the saved `%rbp`, `(wcR (RS Lsw v) D).fp (-8)` (where `bXH` is stated;
the same cells as `wcR (RS Lsw v) D`, `Region.fp_out'`): stack 0's words off `swR` from `FS`; those in
`scc_rt_main`'s region `RS Lsw v` but off `wc_main`'s kept from the call (`CKept`, `Abs`). -/
theorem stackOff_r0_boxH {Lsw D : Int} (hD : 8 ≤ D) (hL : 88 + D ≤ Lsw) (hL1 : Lsw ≤ 16384)
    (hL8 : Lsw % 8 = 0) {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} :
    ∀ m, wcF (RS Lsw v) D (FS (Ly) (RS0) Lsw 0#64 v) m0 σC m →
      Spike.Lib.X64.Flow.Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab) ((wcR (RS Lsw v) D).fp (-8)) m := by
  rintro m ⟨⟨⟨-, ⟨hv, -⟩, hso⟩, -⟩, hck, hA⟩ a h8 ha ha7 hout
  have hst := (Ly).stacks_sub
  have hal := (Ly).stacks_al
  have hf := (Ly).pool_fit
  have hvS := Spike.Lib.X64.WakePh.StartPlaceLy.v_top hpw i hv
  have hr : Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab = RS0 := by
    show (⟨(Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat, 16384⟩ :
      Scc.Sem.Range) = _
    rw [(Ly).lab_stacks]
  rw [hr] at ha ha7
  simp only [Scc.Sem.Range.Sub] at hst
  obtain ⟨hR, hb⟩ := rs_okH (Lsw := Lsw) (v := v) (by omega) (by omega)
  have hbw := Spike.Lib.Region.callee_base (hi' := 8) hR (kc := -80) (lo' := -D)
    (by show 8 - Lsw ≤ -80 + -D; omega) (by omega) (by show (-80 : Int) < 8; decide)
  have hwOK : (wcR (RS Lsw v) D).OK := Spike.Lib.Region.callee_ok hR (by show 8 - Lsw ≤ -80 + -D; omega)
    (by omega) (by show (-80 : Int) < 8; decide) (by show (-80 : Int) + 8 ≤ 8; decide)
  replace hout := Spike.Lib.Region.fp_out' hwOK (by show -D ≤ -8; omega) (by show (-8 : Int) < 8; decide) hout
  have hb' : ((wcR (RS Lsw v) D).base.toNat : Int) = v.toNat + -88 := by
    rw [show wcR (RS Lsw v) D = (RS Lsw v).callee (-80) (-D) 8 from rfl, hbw, hb]
    omega
  rw [hb', show (wcR (RS Lsw v) D).lo = -D from rfl, show (wcR (RS Lsw v) D).hi = 8 from rfl] at hout
  have hca := ha7
  simp only [Scc.Sem.Range.contains, BitVec.add_zero] at hca
  by_cases hin : (a : Int) + 8 ≤ v.toNat + -Lsw ∨ (v.toNat : Int) + 0 ≤ a
  · exact hso a h8 ha ha7 hin
  -- in `scc_rt_main`'s region, off `wc_main`'s: kept from the call
  have hk : (RS Lsw v).Off ((a : Int) - (v.toNat - 8)) :=
    ⟨by omega, by show 8 - Lsw ≤ _; omega, by show _ ≤ (8 : Int); omega⟩
  have he := (RS Lsw v).addr_toNat hR hk
  rw [hb] at he
  have hn : ¬ ((RS Lsw v).callee (-80) (-D) 8).Off ((a : Int) - (v.toNat - 8) - -80) :=
    fun ⟨_, h2, h3⟩ => by
      change -D ≤ _ at h2
      change _ ≤ (8 : Int) at h3
      omega
  obtain ⟨j, hj, -⟩ := hA.slot _ hk
  have ea : BitVec.ofNat 64 a = (RS Lsw v).addr ((a : Int) - (v.toNat - 8)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  rw [ea, hck _ hk hn, hj]; rfl

end Spike.Lib.X64.HelloPh.BoxRF

/-- info: 'Spike.Lib.X64.HelloPh.BoxRF.rtF_of_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.BoxRF.rtF_of_wn

/-- info: 'Spike.Lib.X64.HelloPh.BoxRF.unF_of_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.BoxRF.unF_of_wn

/-- info: 'Spike.Lib.X64.HelloPh.BoxRF.wcF_dmemH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.BoxRF.wcF_dmemH

/-- info: 'Spike.Lib.X64.HelloPh.BoxRF.wcF_takeMemH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.BoxRF.wcF_takeMemH

/-- info: 'Spike.Lib.X64.HelloPh.BoxRF.stackOff_r0_boxH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.BoxRF.stackOff_r0_boxH
