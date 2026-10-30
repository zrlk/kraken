/-
**`wc_main`'s frame condition survives the child's stack take** (AArch64): at the runtime's layout `Ly := RuntimeLayout.ofPlaceW hpw i`,
`h0`'s frame condition `wF (swR v (-384) 0) 336 (FS Ly rS0 384 0 v) m0 σC`
holds after the take copies the child's stack `r1Of` (`Ret0.takeMem`):
`Box`'s `hFt` (`WakeBoxW`, section `Take`) at that frame condition.

The child's stack `r1Of = [stacksA + 16384, +16384)` lies past stack 0
and in the pool (`hsub1_W`, A13's data part `hA13`), so the take changes no
word below `stacksA + 16384` (stack 0's words of `StackOff`, `wc_main`'s
cells kept by `CKept`, all under `v = stacksA + 16384` by `swF`) and no
runtime word (the limit word of `swF`, clear of the pool). `WordsNone` is
`wordsNone_takeMem`.

- `wF_takeMem`: the lemma.
- `stackOff_r0_box`: `Box`'s `StackOff (r0Of lab) R` at that frame condition,
  `R = wR (swR v (-384) 0) 336`: stack 0's words off `swR` from `FS`, those
  between `R`'s top `v - 48` and `v` (`scc_rt_main`'s frame) kept from the
  call (`CKept`, `Abs`).
-/
import Spike.Lib.A64WakeStartPlaceLy

namespace Spike.Lib.A64.WakePh.StartPlaceLy

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow.Ret0 (takeMem)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

/-- The child's stack starts at `stacksA + 16384`, and its end and the
pool's fit the address space. -/
private theorem r1_lo (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab).lo = (Ly).stacksA.toNat + 16384 ∧
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
private theorem below_off (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a.toNat + 8 ≤ (Ly).stacksA.toNat + 16384) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) := by
  intro j hj hm
  obtain ⟨hlo, h32⟩ := r1_lo hpw i hA13
  have hf := (Ly).pool_fit
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
  have hk := List.mem_range.mp hk
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [hlo] at this
  simp only [Spike.Lib.A64.Rt.PreChild.r1Of] at hk
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **A runtime word is off the child's stack**: it is clear of the pool
(`words_pool`), the child's stack inside it (`hsub1_W`). -/
private theorem rt_off (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a ∈ (Ly).rtWords) :
    ∀ j < 8, a + BitVec.ofNat 64 j ∉ Scc.Sem.Kernel.addrs (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) := by
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
  simp only [Spike.Lib.WakeOSide.r1W] at h1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  unfold Spike.Lib.A64.Rt.Clear at hp
  omega

/-- **`Box`'s `hFt` at `h0`'s frame condition**: `wc_main`'s frame
condition at the call (`WakeM.wF`, over `FS` at the first stack, `Lsw =
384`, `D = 336`) is kept by the child's stack take. -/
theorem wF_takeMem (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} :
    ∀ m (pm : _root_.Mem 64),
      Spike.Lib.A64.Flow.WakeM.wF (Spike.Lib.A64.Flow.swR v (-384) 0) 336
        (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC m →
      Spike.Lib.A64.Flow.WakeM.wF (Spike.Lib.A64.Flow.swR v (-384) 0) 336
        (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC
        (takeMem pm (Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab) m) := by
  intro m pm ⟨⟨hwn, ⟨hv, hlim⟩, hso⟩, hck, hA⟩
  obtain ⟨hlo, h32⟩ := r1_lo hpw i hA13
  have hf := (Ly).pool_fit
  have hsub := hsub1_W hpw i hA13
  have hvS : v.toNat = (Ly).stacksA.toNat + 16384 := by
    rw [hv]
    show (Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64 + 16384#64).toNat = _
    rw [(Ly).lab_stacks, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  refine ⟨⟨Spike.Lib.A64.Rt.wordsNoneP_takeMem (PlaceW.wf_link_of_placeW i hpw) hsub hwn, ⟨hv, ?_⟩, ?_⟩, ?_, hA⟩
  · -- the limit word: a runtime word
    have hw : Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) ∈
        (Ly).rtWords := by
      show Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA
        (_root_.Executable.labels (Ly).exe).label + 0#64 + 8#64)) ∈ _
      rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
      exact (Ly).fld_mem (i := 1) (by decide)
    rw [Spike.Lib.A64.Flow.Ret0.loadInt_takeMem (rt_off hpw i hA13 hw)]
    exact hlim
  · -- stack 0's words: below `stacksA + 16384`
    intro a h8 ha ha7 hout
    have hrs : (Spike.Lib.A64.Rt.rS0 (Ly)).lo = (Ly).stacksA.toNat := by
      show ((Ly).stacksA + 0#64).toNat = _
      rw [BitVec.add_zero]
    have hrsz : (Spike.Lib.A64.Rt.rS0 (Ly)).size = 16384 := rfl
    have hrs2 : ((Ly).stacksA + 0#64).toNat = (Ly).stacksA.toNat := by rw [BitVec.add_zero]
    have ha' := ha
    have ha7' := ha7
    simp only [Scc.Sem.Range.contains] at ha' ha7'
    rw [Spike.Lib.A64.Flow.Ret0.loadInt_takeMem (below_off hpw i hA13 (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))]
    exact hso a h8 ha ha7 hout
  · -- `wc_main`'s cells: below `v`
    intro k hk hn
    have hR : (Spike.Lib.A64.Flow.swR v (-384) 0).OK := ⟨by simp [Spike.Lib.A64.Flow.swR]; omega,
      by simp [Spike.Lib.A64.Flow.swR]; omega⟩
    have he := (Spike.Lib.A64.Flow.swR v (-384) 0).addr_toNat hR hk
    have hk2 : k + 8 ≤ 0 := hk.2.2
    simp only [show (Spike.Lib.A64.Flow.swR v (-384) 0).base = v from rfl] at he
    rw [Spike.Lib.A64.Flow.Ret0.loadInt_takeMem (below_off hpw i hA13 (by omega))]
    exact hck k hk hn

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.wF_takeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wF_takeMem

/-- **`Box`'s main stack off its region at `h0`'s frame condition**: every
word of stack 0 (`r0Of`) outside `wc_main`'s region `wR (swR v (-384) 0) 336`
holds a value. -/
theorem stackOff_r0_box {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} :
    ∀ m, Spike.Lib.A64.Flow.WakeM.wF (Spike.Lib.A64.Flow.swR v (-384) 0) 336
        (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC m →
      Spike.Lib.A64.Flow.Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab)
        (Spike.Lib.A64.Flow.WakeM.wR (Spike.Lib.A64.Flow.swR v (-384) 0) 336) m := by
  rintro m ⟨⟨-, ⟨hv, -⟩, hso⟩, hck, hA⟩ a h8 ha ha7 hout
  have hst := (Ly).stacks_sub
  have hal := (Ly).stacks_al
  have hf := (Ly).pool_fit
  have hvS : v.toNat = (Ly).stacksA.toNat + 16384 := by
    rw [hv]
    show (Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64 + 16384#64).toNat = _
    rw [(Ly).lab_stacks]; exact Spike.Lib.A64.Rt.top0_toNat (Ly)
  have hr : Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab = Spike.Lib.A64.Rt.rS0 (Ly) := by
    show (⟨(Spike.Lib.A64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat, 16384⟩ :
      Scc.Sem.Range) = _
    rw [(Ly).lab_stacks]
  rw [hr] at ha ha7
  have hR : (Spike.Lib.A64.Flow.swR v (-384) 0).OK := ⟨by simp [Spike.Lib.A64.Flow.swR]; omega,
    by simp [Spike.Lib.A64.Flow.swR]; omega⟩
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR (kc := -48) (lo' := -336)
    (by simp [Spike.Lib.A64.Flow.swR]) (by decide) (by simp [Spike.Lib.A64.Flow.swR])
  have hb' : ((Spike.Lib.A64.Flow.WakeM.wR (Spike.Lib.A64.Flow.swR v (-384) 0) 336).base.toNat : Int) =
      v.toNat + -48 := hb
  rw [hb', show (Spike.Lib.A64.Flow.WakeM.wR (Spike.Lib.A64.Flow.swR v (-384) 0) 336).lo = -336 from rfl,
    show (Spike.Lib.A64.Flow.WakeM.wR (Spike.Lib.A64.Flow.swR v (-384) 0) 336).hi = 0 from rfl] at hout
  have hca := ha7
  simp only [Scc.Sem.Range.contains] at hca
  by_cases hin : (a : Int) + 8 ≤ v.toNat + -384 ∨ (v.toNat : Int) + 0 ≤ a
  · exact hso a h8 (hr ▸ ha) (hr ▸ ha7) hin
  -- `scc_rt_main`'s frame: `[v - 48, v)`, kept from the call
  have hk : (Spike.Lib.A64.Flow.swR v (-384) 0).Off ((a : Int) - v.toNat) :=
    ⟨by omega, by simp [Spike.Lib.A64.Flow.swR]; omega, by simp [Spike.Lib.A64.Flow.swR]; omega⟩
  have he := (Spike.Lib.A64.Flow.swR v (-384) 0).addr_toNat hR hk
  simp only [show (Spike.Lib.A64.Flow.swR v (-384) 0).base = v from rfl] at he
  have hn : ¬ ((Spike.Lib.A64.Flow.swR v (-384) 0).callee (-48) (-336) 0).Off ((a : Int) - v.toNat - -48) :=
    fun ⟨_, _, h3⟩ => by simp [Spike.Lib.Region.callee] at h3; omega
  obtain ⟨j, hj, -⟩ := hA.slot _ hk
  have ea : BitVec.ofNat 64 a = (Spike.Lib.A64.Flow.swR v (-384) 0).addr ((a : Int) - v.toNat) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  rw [ea, hck _ hk hn, hj]; rfl

/-- info: 'Spike.Lib.A64.WakePh.StartPlaceLy.stackOff_r0_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackOff_r0_box

end Spike.Lib.A64.WakePh.StartPlaceLy
