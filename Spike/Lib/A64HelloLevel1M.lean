/-
**hello's level 1: the box allocation's words free at the start's `FS`** (AArch64): `Level1I.hB_land`'s /
`Level1I.h1_level1`'s `hmem0` at the level's memory sides
`msOfA … I (upd LB l b) (updN (ls0T ls) l n) []`, from `WordsNone` (`StartGlue.hmemB_of_wordsNone`) as
`StartPlace0.hello_rd_place0` discharges it at level 0: the arena (`arOf`, independent of the labels, sizes and
frames) inside `.heap`, its counter inside `.data` (`CtrZ`).

- `hmem0_level1`: `hmem0` at every `l b n`.
-/
import Spike.Lib.A64HelloLevel1I

namespace Spike.Lib.A64.HelloPh.Level1I

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.WakeLoadT (L0T ls0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The level's memory sides after rodata's allocation of `l` at `b`, `n` words, at the frames `fs`. -/
local notation "MS1" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) I (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

/-- **`hmem0` at level 1** (module doc): at every allocation `l b n` of rodata, a box call's counter and headers at
the level's memory side are unloaded under the start's `FS` at the first stack's top. -/
theorem hmem0_level1 (hc : Spike.Lib.A64.Rt.CtrZ o) :
    ∀ l b n, ∀ q : Call, q.OKB ((MS1) l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) l b n []).ctr ∨ ∃ o, o + ((MS1) l b n []).units q.n q.τ ≤ ((MS1) l b n []).cells ∧
        a.toNat = q.hdrAt ((MS1) l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none := by
  intro l b n
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link IH hpw) hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : ((MS1) l b n []).heap = (Ly).Λ.heap.lo := rfl
  have hct : ((MS1) l b n []).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hHi : ((MS1) l b n []).heap + 16 * ((MS1) l b n []).cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size := by
    show _ + 16 * 4194304 ≤ _; rw [hh, ← hA]; omega
  have hctr : Spike.Lib.DmemPriv.WordIn (Ly).Λ.heap ((MS1) l b n []).ctr ∨
      Spike.Lib.DmemPriv.WordIn (Ly).Λ.data ((MS1) l b n []).ctr := by
    rw [hct]; exact .inr ⟨⟨hc1, by omega⟩, ⟨by omega, by omega⟩⟩
  refine Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun _ h => h.1.wn) (Nat.le_of_eq hh.symm)
    hHi hctr ?_
  intro q hq
  have hu : 1 ≤ ((MS1) l b n []).units q.n q.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) hq.toS.accs
  have hf : ((MS1) l b n []).off q.n q.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) hq.toS.accs
  rw [hf]; omega

end Spike.Lib.A64.HelloPh.Level1I

/-- info: 'Spike.Lib.A64.HelloPh.Level1I.hmem0_level1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1I.hmem0_level1
