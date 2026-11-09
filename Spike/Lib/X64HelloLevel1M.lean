/-
**hello's level 1: the box allocation's words free at the start's `FS`** (x86-64; the twin of
`Spike/Lib/A64HelloLevel1M.lean`, same names): `Level1HA.hB_landAg`'s `hmem0` at the level's memory sides
`msOfA … I (upd LB l b) (updN (ls0T ls) l n) []`, from `WordsNone` (`StartGlue.hmemB_of_wordsNone`): the arena
(`arOf`, independent of the labels, sizes and frames) inside `.heap`, its counter inside `.data` (`CtrZ`).

- `hmem0_level1g`: `hmem0` at every `l b n`, at any owned words `own` (the proof reads only the arena and the
  counter).

## Differences from the AArch64 version

- `FS` is `X64.WakePh.MainGlue.FS` at the first stack's top `topS Ly 0` (its `WordsNoneP` at `.1.1`; AArch64:
  `.1`), and the arena's units and header offset are `LowerX64.arOf_units_pos`/`arOf_off_eq`.
- The consumer is `Level1HA.hB_landAg` (AArch64: `Level1I.hB_land`/`h1_level1`, not twinned on x86-64).
- The statement is generic in the owned words (`hmem0_level1g`; AArch64's is at `ownGH` only), so that `ownGHXW`,
  which carries main's and the worker's TCB words, shares it.
-/
import Spike.Lib.X64HelloLevel1I
import Spike.Lib.LowerX64.ArCallMs

namespace Spike.Lib.X64.HelloPh.Level1I

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakePh.MainGlue (FS topS)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- The level's memory sides after rodata's allocation of `l` at `b`, `n` words, at the frames `fs`, at the owned
words `own`. -/
local notation "MS1g" => fun (own : Spike.Lib.X64ConsumerS.OwnS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    own (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-- **`hmem0` at level 1 at any owned words `own`** (module doc): at every allocation `l b n` of rodata, a box
call's counter and headers at the level's memory side are unloaded under the start's `FS` at the first stack's
top. -/
theorem hmem0_level1g {own : Spike.Lib.X64ConsumerS.OwnS} (hc : Spike.Lib.X64.Rt.CtrZ o) :
    ∀ l b n, ∀ q : Call, q.OKB ((MS1g) own l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1g) own l b n []).ctr ∨ ∃ o, o + ((MS1g) own l b n []).units q.n q.τ ≤
        ((MS1g) own l b n []).cells ∧ a.toNat = q.hdrAt ((MS1g) own l b n []) o) →
      ∀ m, FS (Ly) (RS0) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none := by
  intro l b n
  have hL := Spike.Lib.PlaceWX.link IH hpw
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : ((MS1g) own l b n []).heap = (Ly).Λ.heap.lo := rfl
  have hct : ((MS1g) own l b n []).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hHi : ((MS1g) own l b n []).heap + 16 * ((MS1g) own l b n []).cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size := by
    show _ + 16 * 4194304 ≤ _; rw [hh, ← hA]; omega
  have hctr : Spike.Lib.DmemPriv.WordIn (Ly).Λ.heap ((MS1g) own l b n []).ctr ∨
      Spike.Lib.DmemPriv.WordIn (Ly).Λ.data ((MS1g) own l b n []).ctr := by
    rw [hct]; exact .inr ⟨⟨hc1, by omega⟩, ⟨by omega, by omega⟩⟩
  refine Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun _ h => h.1.1.wn) (Nat.le_of_eq hh.symm)
    hHi hctr ?_
  intro q hq
  have hu : 1 ≤ ((MS1g) own l b n []).units q.n q.τ := Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) hq.toS.accs
  have hf : ((MS1g) own l b n []).off q.n q.τ = 8 := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) hq.toS.accs
  rw [hf]; omega

end Spike.Lib.X64.HelloPh.Level1I

/-- info: 'Spike.Lib.X64.HelloPh.Level1I.hmem0_level1g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1I.hmem0_level1g
