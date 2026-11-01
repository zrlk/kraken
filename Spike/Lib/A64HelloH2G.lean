/-
**The box's extra ghost facts at hello's root** (AArch64; `hCI`): the `G`
that `HelloHMid.BoxMH`/`CloneMidH` carry at the ghosts `R`, `F`, `J1`, `t`, pinning `wc_main`'s entry registers as
`HelloLand1.GsH1` does (`HelloJr1`'s pin): `J1` is `wcJ0 (mWC lab σC Jr).J σ1` for a caller's `Jr` whose states hold
rodata's slice at its label `lr` (`SlRegs lbl1 lr`, as `Land.Jr1LH`) and a caller's state `σC` whose slot `-80`
(`mWC`'s `x4`) is main's TCB `pinA + 8`.

- `GJ1H`: the ghost facts.
- `hG_of`: `HelloH2CP.cloneInvH_of_mid`'s `hG` at `G := GJ1H L lbl1 lr` and the placement `upd lbl1 l' b'` placing
  the box `l'` (fresh at `lbl1`), the slice `slWsH lr`, given main's thread-id label at the TCB in `lbl1`.
-/
import Spike.Lib.A64HelloH2CP
import Spike.Lib.A64HelloJr1

namespace Spike.Lib.HelloH2G

open CoreLang CoreTerm
open Spike.Lib (Region Ctl)
open Spike.Lib.A64.Flow (AS)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.Flow.HelloJr1 (SlRegs)

open Spike.Lib.HelloHMid (slWsH)
open Spike.Lib.WakeT1 (mainTidLbl)

/-- **The box's ghost facts at the root**: `wc_main`'s entry invariant `J1` is `mWC`'s at a caller's state `σC`
whose slot `-80` holds main's TCB (`pinA + 8`) and a caller's invariant `Jr` placing rodata's slice at `lr` in
`x0`–`x3` at `lbl1`. -/
def GJ1H (L : RuntimeLayout) (lbl1 : Lbl) (lr : WeakMem.AllocLabel) (_R : Region) (_F : MachineData → Prop)
    (J1 : AS → Ctl → Prop) (_t : UInt64) : Prop :=
  ∃ (σC σ1 : AS) (Jr : AS → Ctl → Prop), σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA L.lab + 0#64 + 8#64 ∧
    (∀ σ c, Jr σ c → SlRegs lbl1 lr σ) ∧ J1 = wcJ0 (mWC L.lab σC Jr).J σ1

/-- **`cloneInvH_of_mid`'s `hG` at `GJ1H`**: at `wc_main`'s entry `x0`–`x3` are rodata's slice `slWsH lr` at the
placement `upd lbl1 l' b'` (the box `l'` fresh at `lbl1`, so `lr ≠ l'`), and `x4` is main's thread-id label's
place (`hmt`: at `lbl1` it is the TCB `pinA + 8`). -/
theorem hG_of {L : RuntimeLayout} {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    (hl' : lbl1 l' = none) (hmt : lbl1 (mainTidLbl 2) = some (L.pinA.toNat + 8)) :
    ∀ R F J1 t, GJ1H L lbl1 lr R F J1 t → ∀ σe c, J1 σe c →
      Spike.Lib.HelloMainPreSrc.SlRep (Spike.Lib.A64ConsumerA.upd lbl1 l' b') (slWsH lr) σe.regs.X0.toNat
        σe.regs.X1.toNat
        σe.regs.X2.toNat σe.regs.X3.toNat ∧
        Spike.Lib.A64ConsumerA.upd lbl1 l' b' (mainTidLbl 2) = some σe.regs.X4.toNat := by
  rintro R F J1 t ⟨σC, σ1, Jr, hslot, hJr, rfl⟩ σe c ⟨rfl, σx, hx, h0, h1, h2, h3, h4, -⟩
  obtain ⟨hl0, hx1, hx2, hx3⟩ := hJr σx c hx
  have hne : lr ≠ l' := by intro h; subst h; rw [hl'] at hl0; cases hl0
  have hne2 : mainTidLbl 2 ≠ l' := by intro h; rw [h, hl'] at hmt; cases hmt
  have hpin : L.pinA.toNat < 2 ^ 32 := L.words_small _ L.pin_mem
  refine ⟨⟨lr, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (if lr = l' then some b' else lbl1 lr) = some σ1.regs.X0.toBitVec.toNat
    split
    · exact absurd ‹_› hne
    · rw [h0]; exact hl0
  · show σ1.regs.X1.toBitVec.toNat = 0
    rw [h1]; exact hx1
  · show σ1.regs.X2.toBitVec.toNat = 2
    rw [h2]; exact hx2
  · show σ1.regs.X3.toBitVec.toNat = 13
    rw [h3]; exact hx3
  · show (if mainTidLbl 2 = l' then some b' else lbl1 (mainTidLbl 2)) = some σ1.regs.X4.toBitVec.toNat
    split
    · exact absurd ‹_› hne2
    · rw [hmt, h4, hslot, Spike.Lib.A64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
      congr 1; omega

end Spike.Lib.HelloH2G

/-- info: 'Spike.Lib.HelloH2G.hG_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2G.hG_of
