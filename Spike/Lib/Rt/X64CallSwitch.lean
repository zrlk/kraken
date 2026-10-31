/-
**A runtime call that changes instance** (x86-64): the `call fn` block of a
caller whose owned words and phase are one instance's (`InstOk` at `own`,
`Tk`, `ph`), into a callee proved under another. The block's phase check
`blkPh` compares the callee's phase with the caller's at one `ph`, so it
cannot pass across instances; instead the block is proved at a **constant
instance** (the owned words `o` and phase `T` the caller holds at the
`call`, phase map constant, `InstOk.const`), and its states are moved
(`BlkW.ownCongr`) to the global map `own'`, `Tk'`, which agrees with `o`,
`T` at the `call` and at its successor, the callee's entry.

- `InstOk.const`: an instance's layout facts at constant owned words, phase
  and phase map.
- `blkPh_const`: `blkPh` at a constant phase map is the pc's `okPc`.
- `call_switch`: the `call fn` block inside the global map's `SFactsSt`.

The twin of `Spike/Lib/Rt/A64CallSwitch.lean`. **Unlike AArch64**: no
16-alignment premise `hal`; the block is located by `blockAtB` at a byte
offset `off`; `call` pushes its return address, so the region must cover the
cell at `sp - 8` (`hcov`).
-/
import Spike.Lib.Rt.X64RtMainU
import Spike.Lib.X64OwnCongr

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (SFactsSt StSucc Agree BlkW.ownCongr)
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Scc.Cert.Rt.X64 (blockAtB)

/-- **An instance's layout facts at constant owned words `o`, phase `T` and
phase map.** -/
theorem InstOk.const {exe : _root_.Executable} {endPc : Int64} {cells : List (Directive × Nat)}
    {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
    {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (o : List (Loc × Val)) (T : Prop) :
    InstOk exe endPc cells lab μ (fun _ => o) (fun _ => T) K okPc (fun _ => 0) kp :=
  ⟨hI.lays, hI.endOk, hI.labOk, fun _ _ _ => ⟨rfl, Iff.rfl⟩, hI.off⟩

/-- **`blkPh` of a `call` at a constant phase map** is its pc's `okPc`. -/
theorem blkPh_const {okPc : Nat → Bool} {lab : Label → Int64} {pc ra : Int64} {fn : Label}
    (hok : okPc pc.toBitVec.toNat = true) : blkPh okPc (fun _ => 0) (fun _ => false) lab pc ra (callB fn) = true := by
  have h1 : pc.toBitVec.toNat % 18446744073709551616 = pc.toBitVec.toNat :=
    Nat.mod_eq_of_lt pc.toBitVec.isLt
  simp [blkPh, cellOff, h1, hok, callB, classify_call]

/-- **The `call fn` block across instances**: at the caller's instance
facts `hI` (its layout and off-site pcs only), the block's code, region
(covering the pushed return address, `hcov`) and source facts, its pc off
the sites (`hok`), after the take (`hsub`, `hSM`), its states are inside
`SFactsSt` at the global map `own'`, `Tk'`, given that map agrees with the
constant `o`, `T` at the `call` and at each of its successors (`hag`, over
the block's facts: the caller's owned words at the `call` are the callee
instance's at its entry). -/
theorem call_switch {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own own' : Own} {Tk Tk' : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
    {lbl : Lbl} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (o : List (Loc × Val)) (T : Prop)
    {R : Region} {F : MachineData → Prop} {n : ND} {l fn : Label} {off : Nat}
    (hb : blockAtB cells l off (callB fn) = true) (he : lab l + Int64.ofNat off = n.pc)
    (hR : R.OK) (hcov : Spike.Lib.offOk R.lo R.hi (n.o.sp - 8) = true) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc n.pc.toBitVec.toNat = true) (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hag : BlkW (fun s _ => Agree (fun _ => o) (fun _ => T) own' Tk' s ∧
      ∀ s', StSucc μ s s' → Agree (fun _ => o) (fun _ => T) own' Tk' s') (fun _ _ => False) exe endPc R
      (fun m => F m ∧ StackM rS m) n (callB fn)) :
    BlkW (fun s _ => SFactsSt Λ μ own' rS Tk' s) K exe endPc R (fun m => F m ∧ StackM rS m) n (callB fn) := by
  have h := blkW_post (Λ := Λ) (rS := rS) (lbl := lbl) (F := F) (hI.const o T) hb he (okBlk_callB fn hcov)
    hR (Int.le_refl _) (Int.le_refl _) hC (ra := 0) (by rw [he]; exact blkPh_const hok)
    (fun _ _ _ k hk hr => (noRet_false (MainU.callB_noRet fn) k hk hr).elim) (fun _ _ _ => rfl) hsub hSM
  have h' : BlkW (fun s _ => SFactsSt Λ μ (fun _ => o) rS (fun _ => T) s) K exe endPc R
      (fun m => F m ∧ StackM rS m) n (callB fn) := fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1.toSt, r.2⟩
  exact BlkW.ownCongr h' hag

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.InstOk.const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.InstOk.const

/-- info: 'Spike.Lib.X64.Rt.blkPh_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.blkPh_const

/-- info: 'Spike.Lib.X64.Rt.call_switch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.call_switch
