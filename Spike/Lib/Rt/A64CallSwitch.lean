/-
**A runtime call that changes instance** (AArch64): the `bl fn` block of a
caller whose owned words and phase are one instance's (`InstOk` at `own`,
`Tk`, `ph`), into a callee proved under another. The block's phase check
`blkPh` compares the callee's phase with the caller's at one `ph`, so it
cannot pass across instances; instead the block is proved at a **constant
instance** (the owned words `o` and phase `T` the caller holds at the
`bl`, phase map constant, `InstOk.const`), and its states are moved
(`BlkW.ownCongr`) to the global map `own'`, `Tk'`, which agrees with `o`,
`T` at the `bl` and at its successor, the callee's entry.

- `InstOk.const`: an instance's layout facts at constant owned words, phase
  and phase map.
- `blkPh_const`: `blkPh` at a constant phase map is the pc's `okPc`.
- `call_switch`: the `bl fn` block inside the global map's `SFactsSt`.
-/
import Spike.Lib.Rt.A64RtMainU
import Spike.Lib.A64OwnCongr

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (SFactsSt StSucc Agree BlkW.ownCongr)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackM)
open Scc.Cert.Rt.A64 (blockAt)

/-- **An instance's layout facts at constant owned words `o`, phase `T` and
phase map.** -/
theorem InstOk.const {exe : _root_.Executable} {endPc : Int64} {prog : List Directive} {lab : Label → Int64}
    {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool}
    {ph : Nat → Nat} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (o : List (Loc × Val)) (T : Prop) :
    InstOk exe endPc prog lab μ (fun _ => o) (fun _ => T) K okPc (fun _ => 0) kp :=
  ⟨hI.lays, hI.endOk, hI.labOk, fun _ _ _ => ⟨rfl, Iff.rfl⟩, hI.off⟩

/-- **`blkPh` of a `bl` at a constant phase map** is its pc's `okPc`. -/
theorem blkPh_const {okPc : Nat → Bool} {lab : Label → Int64} {pc ra : Int64} {fn : Label}
    (hok : okPc pc.toBitVec.toNat = true) : blkPh okPc (fun _ => 0) (fun _ => false) lab pc ra [blD fn] = true := by
  have h1 : pc.toBitVec.toNat % 18446744073709551616 = pc.toBitVec.toNat :=
    Nat.mod_eq_of_lt pc.toBitVec.isLt
  simp [blkPh, h1, hok, blD, Flow.classify, aiTgts]

/-- **The `bl fn` block across instances**: at the caller's instance
facts `hI` (its layout and off-site pcs only), the block's code, region
and source facts, its pc off the sites (`hok`), after the take (`hsub`,
`hSM`), its states are inside `SFactsSt` at the global map `own'`, `Tk'`,
given that map agrees with the constant `o`, `T` at the `bl` and at each of
its successors (`hag`, over the block's facts: the caller's owned words at
the `bl` are the callee instance's at its entry). -/
theorem call_switch {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own own' : Own} {Tk Tk' : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
    {lbl : Lbl} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (o : List (Loc × Val)) (T : Prop)
    {R : Region} {F : MachineData → Prop} {n : ND} {l fn : Label} {k : Nat}
    (hb : blockAt prog l k [blD fn] = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc n.pc.toBitVec.toNat = true) (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hag : BlkW (fun s _ => Agree (fun _ => o) (fun _ => T) own' Tk' s ∧
      ∀ s', StSucc μ s s' → Agree (fun _ => o) (fun _ => T) own' Tk' s') (fun _ _ => False) exe endPc R
      (fun m => F m ∧ StackM rS m) n [blD fn]) :
    BlkW (fun s _ => SFactsSt Λ μ own' rS Tk' s) K exe endPc R (fun m => F m ∧ StackM rS m) n [blD fn] := by
  have h := blkW_post (Λ := Λ) (rS := rS) (lbl := lbl) (F := F) (hI.const o T) hb he (okBlk_blD R.lo R.hi n.o fn)
    hR hal (Int.le_refl _) (Int.le_refl _) hC (ra := 0) (by rw [he]; exact blkPh_const hok)
    (fun _ _ _ k hk r hr => (noRet_false (MainU.blD_noRet fn) k hk r hr).elim) (fun _ _ _ => rfl) hsub hSM
  have h' : BlkW (fun s _ => SFactsSt Λ μ (fun _ => o) rS (fun _ => T) s) K exe endPc R
      (fun m => F m ∧ StackM rS m) n [blD fn] := fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1.toSt, r.2⟩
  exact BlkW.ownCongr h' hag

/-- info: 'Spike.Lib.A64.Rt.call_switch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.call_switch

end Spike.Lib.A64.Rt
