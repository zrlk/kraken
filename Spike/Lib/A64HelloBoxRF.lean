/-
**hello.w's box region and frame condition facts** (AArch64): the twins of wake's
`StartPlaceLy.wF_takeMem`/`stackOff_r0_box` and `WakeBoxW.fS_dmem`/`wF_dmem` at hello's `wc_main` frame condition
at the call, `wcF (swR v (-helloLsw) 0) helloD (FS Ly rS0 helloLsw 0 v) m1 σ1` (`scc_rt_main`'s frame `80`, the
region `helloD = 400` deep, the switched stack `helloLsw = 480` deep), and the runtime's words unmapped under it.
These are `HelloH1A.H1GAH`'s region/frame fields at the box's real ghost (`RootHP.hP_of`).

- `rtF_of_wn`: `WordsNoneP` gives `rtF` (every runtime word's bytes are in `.data` or `pinned`, `words_mapped`).
- `unF_of_wn`: `WordsNoneP` gives the second TCB's words (`tH = pinA + 144`, six words) unmapped, given the pinned
  region reaches `pinA + 200` (`hpin2`).
- `wcF_dmemH`: the frame condition reads memory only (`fcg`).
- `wcF_takeMemH`: the frame condition survives the child's stack take (`fcl`).
- `stackOff_r0_boxH`: main's stack mapped off `wc_main`'s region under it (`hF0`).
-/
import Spike.Lib.A64HelloBox
import Spike.Lib.A64WakeTakeFLy
import Spike.Lib.PlaceWRt

namespace Spike.Lib.A64.HelloPh.BoxRF

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (takeMem)
open Spike.Lib.A64.Flow.HelloM (wcR wcF)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.DmemPriv (WordsNoneP)

/-! ## The runtime's words under `WordsNoneP` -/

/-- **`WordsNoneP` gives `rtF`**: each runtime word's bytes lie in `.data` or `pinned` (`words_mapped`), both
private. -/
theorem rtF_of_wn (L : RuntimeLayout) {m : MachineData} (h : WordsNoneP L.Λ m.dmem) : Spike.Lib.A64.Rt.rtF L m :=
  fun a ha => h a fun j hj => ((L.words_mapped a ha).2.2 j hj).elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- **`WordsNoneP` gives the second TCB's words unmapped** (`H1GAH.hunF`): `tH = pinA + 144` and its six words lie
in `[pinA + 144, pinA + 192)`, inside the pinned region (`pinA` its base, `hpin2` its reach). -/
theorem unF_of_wn (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {m : MachineData}
    (h : WordsNoneP (Ly).Λ m.dmem) :
    ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (Spike.Lib.A64.Flow.HelloWc.tH (Ly).lab), Mem.loadInt m.dmem a 8 = none := by
  have hp0 : (Ly).pinA.toNat = (Ly).Λ.pinned.lo := Spike.Lib.PlaceW.pinA_toNat_ofPlaceW hpw i
  have hs := (Ly).words_small _ (Ly).pin_mem
  have hT : (Spike.Lib.A64.Flow.HelloWc.tH (Ly).lab).toNat = (Ly).pinA.toNat + 144 := by
    show (Spike.Lib.A64.Flow.Ret0.pinA (_root_.Executable.labels (Ly).exe).label + 144#64).toNat = _
    rw [(Ly).lab_pin, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  intro a ha
  apply h
  have hk : ∃ k < 6, a = Spike.Lib.A64.Flow.HelloWc.tH (Ly).lab + BitVec.ofNat 64 (8 * k) := by
    simp only [Spike.Lib.A64.Rt.Ti.tiAddrs, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with h | h | h | h | h | h <;> exact ⟨_, by decide, h⟩
  obtain ⟨k, hk, rfl⟩ := hk
  intro j hj
  have ha : (Spike.Lib.A64.Flow.HelloWc.tH (Ly).lab + BitVec.ofNat 64 (8 * k)).toNat =
      (Ly).pinA.toNat + 144 + 8 * k := by
    rw [BitVec.toNat_add, hT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [ha]
  unfold Spike.Lib.DmemPriv.PrivB Scc.Sem.Range.contains
  omega

/-! ## `wc_main`'s frame condition at the call -/

/-- **The frame condition reads memory only** (`H1GAH.fcg`; wake's `WakeBoxW.fS_dmem`/`wF_dmem`). -/
theorem wcF_dmemH {R : Spike.Lib.Region} {D : Int} {L : RuntimeLayout} {rS : Scc.Sem.Range} {Lsw : Int}
    {k0 v : BitVec 64} {m1 : MachineData} {σ1 : Spike.Lib.A64.Flow.AS} :
    ∀ m m' : MachineData, m'.dmem = m.dmem → wcF R D (FS L rS Lsw k0 v) m1 σ1 m → wcF R D (FS L rS Lsw k0 v) m1 σ1 m' :=
  fun _ _ e h => ⟨by
      simpa only [Spike.Lib.A64.WakePh.MainGlue.FS, Spike.Lib.A64.Rt.swFSL, Spike.Lib.A64.Flow.Ret0.swF,
        Spike.Lib.A64.Flow.Ret0.StackOff, e] using h.1,
    fun k hk hn => by rw [e]; exact h.2.1 k hk hn, h.2.2⟩

/-- The child's stack starts at `stacksA + 16384`, and its end and the pool's fit the address space. -/
private theorem r1_loH (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    (R1).lo = (Ly).stacksA.toNat + 16384 ∧
      (Ly).stacksA.toNat + 32768 ≤ (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size := by
  have h32 : (Ly).stacksA.toNat + 32768 ≤ (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size := by
    simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
    exact hA13.2
  have hf := (Ly).pool_fit
  refine ⟨?_, h32⟩
  unfold Spike.Lib.A64.Rt.PreChild.r1Of RuntimeLayout.lab
  rw [(Ly).lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

/-- **A word below `stacksA + 16384` is off the child's stack.** -/
private theorem below_offH (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a.toNat + 8 ≤ (Ly).stacksA.toNat + 16384) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (R1) := by
  intro j hj hm
  obtain ⟨hlo, h32⟩ := r1_loH hpw i hA13
  have hf := (Ly).pool_fit
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  have hk := List.mem_range.mp hk
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [hlo] at this
  simp only [Spike.Lib.A64.Rt.PreChild.r1Of] at hk
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **A runtime word is off the child's stack**: it is clear of the pool (`words_pool`), the child's stack inside
it (`hsub1_W`). -/
private theorem rt_offH (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a ∈ (Ly).rtWords) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (R1) := by
  intro j hj hm
  have hsub := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hpw i hA13
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  have hk := List.mem_range.mp hk
  have hs := (Ly).words_small a ha
  have hp := (Ly).words_pool a ha
  have hf := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := hsub
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  simp only [Spike.Lib.WakeOSide.r1W] at h1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  unfold Spike.Lib.A64.Rt.Clear at hp
  omega

/-- **The frame condition survives the child's stack take** (`H1GAH.fcl`; wake's `StartPlaceLy.wF_takeMem` at
`helloLsw`/`helloD`): `WordsNoneP` by `wordsNoneP_takeMem`, the limit word a runtime word, stack 0's words and
`wc_main`'s cells below `stacksA + 16384`, all off the child's stack. -/
theorem wcF_takeMemH (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} :
    ∀ m (pm : _root_.Mem 64),
      wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m →
      wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m0 σC (takeMem pm (R1) m) := by
  intro m pm ⟨⟨hwn, ⟨hv, hlim⟩, hso⟩, hck, hA⟩
  have hL : helloLsw = 480 := rfl
  obtain ⟨hlo, h32⟩ := r1_loH hpw i hA13
  have hf := (Ly).pool_fit
  have hsub := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hpw i hA13
  have hvS : v.toNat = (Ly).stacksA.toNat + 16384 := by
    rw [hv]
    show (Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64 + 16384#64).toNat = _
    rw [(Ly).lab_stacks, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  refine ⟨⟨Spike.Lib.A64.Rt.wordsNoneP_takeMem (Spike.Lib.PlaceW.wf_link_of_placeW i hpw) hsub hwn, ⟨hv, ?_⟩, ?_⟩,
    ?_, hA⟩
  · -- the limit word: a runtime word
    have hw : Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) ∈
        (Ly).rtWords := by
      show Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA
        (_root_.Executable.labels (Ly).exe).label + 0#64 + 8#64)) ∈ _
      rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
      exact (Ly).fld_mem (i := 1) (by decide)
    rw [Spike.Lib.A64.Flow.Ret0.loadInt_takeMem (rt_offH hpw i hA13 hw)]
    exact hlim
  · -- stack 0's words: below `stacksA + 16384`
    intro a h8 ha ha7 hout
    have hrs : (RS).lo = (Ly).stacksA.toNat := by
      show ((Ly).stacksA + 0#64).toNat = _
      rw [BitVec.add_zero]
    have hrsz : (RS).size = 16384 := rfl
    have hrs2 : ((Ly).stacksA + 0#64).toNat = (Ly).stacksA.toNat := by rw [BitVec.add_zero]
    have ha' := ha
    have ha7' := ha7
    simp only [Scc.Sem.Range.contains] at ha' ha7'
    rw [Spike.Lib.A64.Flow.Ret0.loadInt_takeMem (below_offH hpw i hA13 (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))]
    exact hso a h8 ha ha7 hout
  · -- `wc_main`'s cells: below `v`
    intro k hk hn
    have hR : (swR v (-helloLsw) 0).OK := ⟨by simp [swR, helloLsw]; omega, by simp [swR]; omega⟩
    have he := (swR v (-helloLsw) 0).addr_toNat hR hk
    have hk2 : k + 8 ≤ 0 := hk.2.2
    simp only [show (swR v (-helloLsw) 0).base = v from rfl] at he
    rw [Spike.Lib.A64.Flow.Ret0.loadInt_takeMem (below_offH hpw i hA13 (by omega))]
    exact hck k hk hn

/-- **Main's stack mapped off `wc_main`'s region** (`H1GAH.hF0`; wake's `StartPlaceLy.stackOff_r0_box` at
`helloLsw`/`helloD`): stack 0's words off `swR` from `FS`, those between the region's top `v - 80` and `v`
(`scc_rt_main`'s frame) kept from the call (`CKept`, `Abs`). -/
theorem stackOff_r0_boxH {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} :
    ∀ m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m →
      Spike.Lib.A64.Flow.Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab) (wcR (swR v (-helloLsw) 0) helloD) m := by
  rintro m ⟨⟨-, ⟨hv, -⟩, hso⟩, hck, hA⟩ a h8 ha ha7 hout
  have hL : helloLsw = 480 := rfl
  have hD : helloD = 400 := rfl
  have hst := (Ly).stacks_sub
  have hal := (Ly).stacks_al
  have hf := (Ly).pool_fit
  have hvS : v.toNat = (Ly).stacksA.toNat + 16384 := by
    rw [hv]
    show (Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64 + 16384#64).toNat = _
    rw [(Ly).lab_stacks]; exact Spike.Lib.A64.Rt.top0_toNat (Ly)
  have hr : Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab = RS := by
    show (⟨(Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat, 16384⟩ :
      Scc.Sem.Range) = _
    rw [(Ly).lab_stacks]
  rw [hr] at ha ha7
  have hR : (swR v (-helloLsw) 0).OK := ⟨by simp [swR, helloLsw]; omega, by simp [swR]; omega⟩
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (kc := -80) (lo' := -helloD)
    (by simp [swR, helloLsw, helloD]) (by decide) (by simp [swR, helloLsw])
  have hb' : ((wcR (swR v (-helloLsw) 0) helloD).base.toNat : Int) = v.toNat + -80 := hb
  rw [hb', show (wcR (swR v (-helloLsw) 0) helloD).lo = -helloD from rfl,
    show (wcR (swR v (-helloLsw) 0) helloD).hi = 0 from rfl] at hout
  have hca := ha7
  simp only [Scc.Sem.Range.contains] at hca
  by_cases hin : (a : Int) + 8 ≤ v.toNat + -helloLsw ∨ (v.toNat : Int) + 0 ≤ a
  · exact hso a h8 ha ha7 hin
  -- `scc_rt_main`'s frame: `[v - 80, v)`, kept from the call
  have hk : (swR v (-helloLsw) 0).Off ((a : Int) - v.toNat) :=
    ⟨by omega, by simp [swR, helloLsw]; omega, by simp [swR, helloLsw]; omega⟩
  have he := (swR v (-helloLsw) 0).addr_toNat hR hk
  simp only [show (swR v (-helloLsw) 0).base = v from rfl] at he
  have hn : ¬ ((swR v (-helloLsw) 0).callee (-80) (-helloD) 0).Off ((a : Int) - v.toNat - -80) :=
    fun ⟨_, _, h3⟩ => by simp [Spike.Lib.Region.callee] at h3; omega
  obtain ⟨j, hj, -⟩ := hA.slot _ hk
  have ea : BitVec.ofNat 64 a = (swR v (-helloLsw) 0).addr ((a : Int) - v.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  rw [ea, hck _ hk hn, hj]; rfl

end Spike.Lib.A64.HelloPh.BoxRF

/-- info: 'Spike.Lib.A64.HelloPh.BoxRF.rtF_of_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.BoxRF.rtF_of_wn

/-- info: 'Spike.Lib.A64.HelloPh.BoxRF.unF_of_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.BoxRF.unF_of_wn

/-- info: 'Spike.Lib.A64.HelloPh.BoxRF.wcF_dmemH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.BoxRF.wcF_dmemH

/-- info: 'Spike.Lib.A64.HelloPh.BoxRF.wcF_takeMemH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.BoxRF.wcF_takeMemH

/-- info: 'Spike.Lib.A64.HelloPh.BoxRF.stackOff_r0_boxH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.BoxRF.stackOff_r0_boxH
