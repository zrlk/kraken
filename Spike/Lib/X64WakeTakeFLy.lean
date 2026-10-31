/-
**`wc_main`'s frame condition survives the child's stack take** (x86-64):
at the runtime's layout `Ly := RuntimeLayout.ofPlaceWX hpw i`, `h0`'s frame
condition `wF (RS wcLsw v) wcD (FS Ly rS0 wcLsw 0 v) m0 σC` holds after the
take copies the child's stack `r1Of` (`Ret0.takeMem`): `Box`'s `hFt`
(`WakeBox.BoxPre`) at that frame condition.

The child's stack `r1Of = [stacksA + 16384, +16384)` lies past stack 0
and in the pool (`hsub1_W`, A13's data part `hA13`), so the take changes no
word below `stacksA + 16384` (stack 0's words of `StackOff`, the switch
region's cells of `CallerCells`, `wc_main`'s cells kept by `CKept`, all
under `v = stacksA + 16384` by `swF`) and no runtime word (the limit word of
`swF`, clear of the pool). `WordsNoneP` is `wordsNoneP_takeMem`.

- `wF_takeMem`: the lemma.
- `stackOff_r0_box`: `Box`'s `StackOff (r0Of lab) R` at that frame condition,
  `R = wR (RS wcLsw v) wcD`: stack 0's words off `swR` from `FS`, those
  between `R`'s top `v - 48` and `v` (`scc_rt_main`'s frame) kept from the
  call (`CKept`, `Abs`).
- `stackOff_r0_boxFp`: the same at `R.fp (-8)` (`Box`'s region in `hxa`),
  which covers the same addresses.

Where x86-64 differs from AArch64: AArch64's frame condition is at
`swR v (-384) 0` and `wR … 336` (`A64WakeTakeFLy`); x86-64's `wc_main` is
called from `scc_rt_main`'s region `RS wcLsw v = (swR v (-384) 0).callee (-8)
(-376) 8` (the return address at `v - 8`) at depth `wcD = 328`, so `wR` is
`[v - 384, v - 48)` and `FS` also carries the switch region's
`CallerCells`, kept by the take as the other words below `v`. The limit
word is `limA (tpOf (tcbS Ly))` (the TCB pointer, not a `UInt64.ofBitVec`).
The extra `stackOff_r0_boxFp` serves `hxa`'s region `(wR …).fp (-8)`.
-/
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64WakeTi2Box
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.RegionFp

namespace Spike.Lib.X64.WakePh.StartPlaceLy

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0 (takeMem)
open Spike.Lib.X64.WakePh.MainGlue (FS RS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

/-- The pool reaches the second stack's end (A13's data part). -/
private theorem pool_32 (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    (Ly).stacksA.toNat + 32768 ≤ (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size := by
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
  exact hA13.2

/-- **A word below `stacksA + 16384` is off the child's stack.** -/
private theorem below_off (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a.toNat + 8 ≤ (Ly).stacksA.toNat + 16384) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) := by
  intro j hj hm
  have hlo := Spike.Lib.X64.WakePh.Ti2.r1_lo (L := Ly)
  have h32 := pool_32 hpw i hA13
  have hf := (Ly).pool_fit
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  have hk := List.mem_range.mp hk
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [hlo] at this
  simp only [Spike.Lib.X64.Rt.PreChild.r1Of] at hk
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **A runtime word is off the child's stack**: it is clear of the pool
(`words_pool`), the child's stack inside it (`hsub1_W`). -/
private theorem rt_off (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a ∈ (Ly).rtWords) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) := by
  intro j hj hm
  have hsub := hsub1_W hpw i hA13
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

/-- The switch base `v` of `FS` at the first stack is its top. -/
theorem v_top {v : BitVec 64} (hv : v = Spike.Lib.X64.WakePh.MainGlue.topS (Ly) 0#64) :
    v.toNat = (Ly).stacksA.toNat + 16384 := by
  rw [hv]
  show (Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64 + 16384#64).toNat = _
  rw [(Ly).lab_stacks]; exact Spike.Lib.X64.Rt.top0_toNat (Ly)

/-- `scc_rt_main`'s region at the switch base `v`, high enough, does not
wrap, and its base is `v - 8`. -/
theorem rs_ok {v : BitVec 64} (hv : 384 ≤ v.toNat) :
    (RS 384 v).OK ∧ ((RS 384 v).base.toNat : Int) = v.toNat + -8 := by
  have hR : (Spike.Lib.X64.swR v (-384) 0).OK :=
    ⟨by simp [Spike.Lib.X64.swR]; omega, by simp [Spike.Lib.X64.swR]; omega⟩
  exact ⟨Spike.Lib.Region.callee_ok hR (by simp [Spike.Lib.X64.swR]) (by decide)
      (by simp [Spike.Lib.X64.swR]) (by simp [Spike.Lib.X64.swR]),
    Spike.Lib.Region.callee_base hR (by simp [Spike.Lib.X64.swR]) (by decide) (by simp [Spike.Lib.X64.swR])⟩

/-- **`Box`'s `hFt` at `h0`'s frame condition**: `wc_main`'s frame
condition at the call (`WakeM.wF`, over `FS` at the first stack, `Lsw =
384`, `D = 328`) is kept by the child's stack take. -/
theorem wF_takeMem (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} :
    ∀ m (pm : _root_.Mem 64),
      Spike.Lib.X64.Flow.WakeM.wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC m →
      Spike.Lib.X64.Flow.WakeM.wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC
        (takeMem pm (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) m) := by
  rw [StartFacts.wcD_eq.1, StartFacts.wcD_eq.2]
  intro m pm ⟨⟨⟨hwn, ⟨hv, hlim⟩, hso⟩, hcc⟩, hck, hA⟩
  have hsub := hsub1_W hpw i hA13
  have hvS := v_top hpw i hv
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
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (rt_off hpw i hA13 hw)]
    exact hlim
  · -- stack 0's words: below `stacksA + 16384`
    intro a h8 ha ha7 hout
    have ha7' := ha7
    simp only [Scc.Sem.Range.contains, BitVec.add_zero] at ha7'
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (below_off hpw i hA13 (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))]
    exact hso a h8 ha ha7 hout
  · -- the switch region's cells: below `v`
    intro k hk hn
    have hR : (Spike.Lib.X64.swR v (-384) 0).OK :=
      ⟨by simp [Spike.Lib.X64.swR]; omega, by simp [Spike.Lib.X64.swR]; omega⟩
    have he := (Spike.Lib.X64.swR v (-384) 0).addr_toNat hR hk
    have hk2 : k + 8 ≤ 0 := hk.2.2
    simp only [show (Spike.Lib.X64.swR v (-384) 0).base = v from rfl] at he
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (below_off hpw i hA13 (by omega))]
    exact hcc k hk hn
  · -- `wc_main`'s cells: below `v`
    intro k hk hn
    obtain ⟨hR, hb⟩ := rs_ok (v := v) (by omega)
    have he := (RS 384 v).addr_toNat hR hk
    have hk2 : k + 8 ≤ 8 := hk.2.2
    rw [hb] at he
    rw [Spike.Lib.X64.Flow.Ret0.loadInt_takeMem (below_off hpw i hA13 (by omega))]
    exact hck k hk hn

set_option linter.unusedSimpArgs false in
/-- **`Box`'s main stack off its region at `h0`'s frame condition**: every
word of stack 0 (`r0Of`) outside `wc_main`'s region `wR (RS wcLsw v) wcD`
holds a value. -/
theorem stackOff_r0_box {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} :
    ∀ m, Spike.Lib.X64.Flow.WakeM.wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC m →
      Spike.Lib.X64.Flow.Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab)
        (Spike.Lib.X64.Flow.WakeM.wR (RS wcLsw v) wcD) m := by
  rw [StartFacts.wcD_eq.1, StartFacts.wcD_eq.2]
  rintro m ⟨⟨⟨-, ⟨hv, -⟩, hso⟩, -⟩, hck, hA⟩ a h8 ha ha7 hout
  have hst := (Ly).stacks_sub
  have hf := (Ly).pool_fit
  have hvS := v_top hpw i hv
  have hr : Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab = Spike.Lib.X64.Rt.rS0 (Ly) := by
    show (⟨(Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat, 16384⟩ :
      Scc.Sem.Range) = _
    rw [(Ly).lab_stacks]
  rw [hr] at ha ha7
  obtain ⟨hR, hb⟩ := rs_ok (v := v) (by simp only [Scc.Sem.Range.Sub] at hst; omega)
  have hbw := Spike.Lib.Region.callee_base (hi' := 8) hR (kc := -48) (lo' := -328)
    (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
  have hb' : ((Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).base.toNat : Int) = v.toNat + -56 := by
    rw [show Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328 = (RS 384 v).callee (-48) (-328) 8 from rfl, hbw, hb]
    omega
  rw [hb', show (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).lo = -328 from rfl,
    show (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).hi = 8 from rfl] at hout
  have hal := (Ly).stacks_al
  have hca := ha7
  simp only [Scc.Sem.Range.contains, BitVec.add_zero] at hca
  by_cases hin : (a : Int) + 8 ≤ v.toNat + -384 ∨ (v.toNat : Int) + 0 ≤ a
  · exact hso a h8 ha ha7 hin
  -- `scc_rt_main`'s frame: `[v - 48, v)`, kept from the call
  have hk : (RS 384 v).Off ((a : Int) - (v.toNat - 8)) :=
    ⟨by omega, by show -376 ≤ _; omega, by show _ ≤ (8 : Int); omega⟩
  have he := (RS 384 v).addr_toNat hR hk
  rw [hb] at he
  have hn : ¬ ((RS 384 v).callee (-48) (-328) 8).Off ((a : Int) - (v.toNat - 8) - -48) :=
    fun ⟨_, _, h3⟩ => by simp [Spike.Lib.Region.callee] at h3; omega
  obtain ⟨j, hj, -⟩ := hA.slot _ hk
  have ea : BitVec.ofNat 64 a = (RS 384 v).addr ((a : Int) - (v.toNat - 8)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  rw [ea, hck _ hk hn, hj]; rfl

set_option linter.unusedSimpArgs false in
/-- **`stackOff_r0_box` at `hxa`'s region** `(wR (RS wcLsw v) wcD).fp (-8)`:
the same addresses `[v - 384, v - 48)`. -/
theorem stackOff_r0_boxFp {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} :
    ∀ m, Spike.Lib.X64.Flow.WakeM.wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC m →
      Spike.Lib.X64.Flow.Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab)
        ((Spike.Lib.X64.Flow.WakeM.wR (RS wcLsw v) wcD).fp (-8)) m := by
  rw [StartFacts.wcD_eq.1, StartFacts.wcD_eq.2]
  intro m hm a h8 ha ha7 hout
  obtain ⟨⟨⟨-, ⟨hv, -⟩, -⟩, -⟩, -, -⟩ := id hm
  have hst := (Ly).stacks_sub
  have hf := (Ly).pool_fit
  have hvS := v_top hpw i hv
  obtain ⟨hR, hb⟩ := rs_ok (v := v) (by simp only [Scc.Sem.Range.Sub] at hst; omega)
  have hRw : (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).OK :=
    Spike.Lib.Region.callee_ok hR (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
  have hbw := Spike.Lib.Region.callee_base (hi' := 8) hR (kc := -48) (lo' := -328)
    (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
  have hb' : ((Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).base.toNat : Int) = v.toNat + -56 := by
    rw [show Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328 = (RS 384 v).callee (-48) (-328) 8 from rfl, hbw, hb]
    omega
  have hbf := Spike.Lib.Region.callee_base (hi' := 16) hRw (kc := -8) (lo' := -320)
    (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
  have hbf' : (((Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).fp (-8)).base.toNat : Int) = v.toNat + -64 := by
    rw [show (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).fp (-8) =
      (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).callee (-8) (-320) 16 from rfl, hbf, hb']
    omega
  rw [hbf', show ((Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).fp (-8)).lo = -320 from rfl,
    show ((Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).fp (-8)).hi = 16 from rfl] at hout
  refine stackOff_r0_box hpw i m hm a h8 ha ha7 ?_
  rw [StartFacts.wcD_eq.1, StartFacts.wcD_eq.2, hb', show (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).lo = -328 from rfl,
    show (Spike.Lib.X64.Flow.WakeM.wR (RS 384 v) 328).hi = 8 from rfl]
  omega

end Spike.Lib.X64.WakePh.StartPlaceLy

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.wF_takeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.wF_takeMem

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.stackOff_r0_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.stackOff_r0_box

/-- info: 'Spike.Lib.X64.WakePh.StartPlaceLy.stackOff_r0_boxFp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlaceLy.stackOff_r0_boxFp
