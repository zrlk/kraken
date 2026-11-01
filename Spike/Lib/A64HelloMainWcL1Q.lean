/-
**`MainWcPS.hlim`, `hbox`, `hcell0` at `Level1I`'s choices** (AArch64; `Level1I.hP`'s fields, stage 3):
at any `PlaceW` output's runtime layout `Ly := RuntimeLayout.ofPlaceW hpw i`, the arena `WakeOD.arW hpw i`, hello's
value invariant `HelloGOf2H.gWH hpw i (WakeHG.cTW hpw i)`, any marks `μ` (so no certificate text), and the level's
labels `upd (L0T Ly.Λ) l b` / `updN (ls0T ls) l n` at an allocation `AllocLand` of rodata's (the label `l` fresh).

- `rtWords_offArW`: the runtime's words are off the arena (`.data`/pinned, both disjoint from the heap).
- `rtFree_L1`: no label of the level covers a runtime word (`StartPlaceLy.hfree_W` off `l`, the arena on it).
- `hlim_L1`: `hlim` at `wc_main`'s entry `JrT Jr TV (swR TOP (-helloLsw) 0)`: the first TCB's limit word under the
  start's `FS`, bounded by `TOP - 224` (`HelloGOf2H.room_gWH_top`).
- `box_c0H`: a box call at `c0H` boxes `z`, an `int` word `0`.
- `hbox_L1`, `hcell0_L1`: `hbox`, `hcell0` at any `Jr1` whose controls are `c0H`'s (`Land.Jr1LH`'s).
-/
import Spike.Lib.A64HelloStartH0
import Spike.Lib.A64HelloHrdR
import Spike.Lib.A64HelloMainPostT
import Spike.Lib.A64HelloLand1
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.MainWcL1Q

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (lrange)
open Spike.Lib.A64.Rt (RuntimeLayout RtFree)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (LimOk)
open Spike.Lib.A64.Flow.HelloM (JrT)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The memory side at hello's choices, any marks, fragment, labels and frames. -/
local notation "MS" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.HelloGOf2H.gWH hpw i (Spike.Lib.WakeHG.cTW hpw i)) own (AR) I lbl lsize fs

/-! ## The runtime's words at the level's labels -/

/-- **The runtime's words are off the arena** `arW`: their first bytes lie in `.data` or pinned (`words_mapped`),
both disjoint from the heap (A1), which holds the arena (`ArenaW.arOf_sub`). -/
theorem rtWords_offArW : ∀ a ∈ (Ly).rtWords, ¬ ((AR).heap ≤ a.toNat ∧ a.toNat < (AR).heap + 16 * (AR).cells) := by
  intro a ha
  have hs : (Scc.Sem.Range.mk (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap (16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells)).Sub
      (Ly).Λ.heap := Spike.Lib.A64.Rt.ArenaW.arOf_sub (Spike.Lib.PlaceW.link i hpw)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hD := hwf.disjoint.2.2.2.1
  have hP := hwf.disjoint.2.2.2.2.2.2.2.2.1
  have hb := ((Ly).words_mapped a ha).2.2 0 (by omega)
  change (Ly).Λ.data.contains (a.toNat + 0) ∨ (Ly).Λ.pinned.contains (a.toNat + 0) at hb
  change ¬ ((Spike.Lib.A64.Rt.arOf (Ly).Λ).heap ≤ a.toNat ∧
    a.toNat < (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells)
  simp only [Scc.Sem.Range.Sub, Scc.Sem.Range.Disjoint, Scc.Sem.Range.contains] at hs hD hP hb
  omega

/-- **No label of the level covers a runtime word**: off the fresh label `l` the start's (`StartPlaceLy.hfree_W`,
no static label); `l`'s `n` words at `b` lie in the arena (`AllocLand`), off the runtime's words. -/
theorem rtFree_L1 (hstat : Λ0.static = fun _ => none) (ls : Lsize) {l : WeakMem.AllocLabel} {b n : Nat}
    (hb : AllocLand (AR).heap (AR).cells b n) :
    RtFree (Ly) (Spike.Lib.A64ConsumerA.upd (L0T (Ly).Λ) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) := by
  rintro a ha ⟨l', b', h1, h2⟩
  by_cases e : l' = l
  · subst e
    simp only [Spike.Lib.A64ConsumerA.upd, Spike.Lib.A64ConsumerA.updN, ite_true, Option.some.injEq, lrange,
      Scc.Sem.Range.contains] at h1 h2
    have := rtWords_offArW hpw i a ha
    obtain ⟨hb1, hb2, -⟩ := hb
    omega
  · simp only [Spike.Lib.A64ConsumerA.upd, e, ite_false] at h1
    simp only [lrange, Spike.Lib.A64ConsumerA.updN, e, ite_false] at h2
    exact Spike.Lib.A64.WakePh.StartPlaceLy.hfree_W hpw i hstat ls a ha ⟨l', b', h1, h2⟩

/-! ## `hlim` -/

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
  {I : Spike.Lib.A64ConsumerS.InvS} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **`hlim` at `wc_main`'s entry** (`MainWcPS.hlim`): at `JrT Jr TV (swR TOP (-helloLsw) 0)` (main's thread pointer,
`sp` at the region's `-80`), the first TCB's limit word is the runtime's (`hfree`), mapped, unloaded under the
start's `FS` (`HrdR.hun_FS`), and every value hello's invariant admits there is at most `sp - 144 = TOP - 224`. -/
theorem hlim_L1 (hfree : RtFree (Ly) lbl lsize) {Jr : FAS → Spike.Lib.Ctl → Prop} :
    ∀ σ c, JrT Jr (TV) (swR (TOP) (-helloLsw) 0) σ c →
      LimOk (MS) (FS (Ly) (RS) helloLsw 0#64 (TOP)) (Ly).exe (Ly).endPc (Spike.Lib.A64.Flow.tcbA σ.regs 8)
        (σ.regs.SP.toBitVec - (144 : Int64).toBitVec) := by
  rintro σ c ⟨-, htp, hsp⟩
  rw [Spike.Lib.A64.Flow.Ret0.tcbA_limA htp, hsp]
  have e : (swR (TOP) (-helloLsw) 0).addr (-80) - (144 : Int64).toBitVec = TOP - (224 : Int64).toBitVec := by
    show (TOP) + BitVec.ofInt 64 (-80) - (144 : Int64).toBitVec = (TOP) - (224 : Int64).toBitVec
    generalize TOP = x
    rw [show BitVec.ofInt 64 (-80) = 18446744073709551536#64 from rfl, show (144 : Int64).toBitVec = 144#64 from rfl,
      show (224 : Int64).toBitVec = 224#64 from rfl]
    bv_omega
  rw [e]
  have hun := Spike.Lib.A64.HelloPh.HrdR.hun_FS (L := Ly) (rS := RS) (Lsw := helloLsw) (k0 := 0#64) (v := TOP)
  have hroom := Spike.Lib.HelloGOf2H.room_gWH_top (L := Ly) (m0 := Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs)
    (Z := 224) (Spike.Lib.A64.WakePh.StartPlaceLy.hcT_W hpw i) (Spike.Lib.PlaceW.limInit_ofPlaceW hpw i)
    (by decide)
  rw [(Ly).lab_pin] at hun ⊢
  have h := Spike.Lib.A64.Rt.rt_limOk (μ := μ) (rd := rd)
    (G := Spike.Lib.HelloGOf2H.gWH hpw i (Spike.Lib.WakeHG.cTW hpw i)) (own := fun s => own s fs) hfree hroom
  exact ⟨h.rt, h.mp, hun, h.room⟩

/-! ## The box at `c0H`: `hbox`, `hcell0` -/

/-- **A box call at `c0H` boxes `z`**: its argument is `z`, of type `int`, one word `0`. -/
theorem box_c0H {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64} {q : Call} (hq : q.OKB ms lab)
    {w0 w1 w2 mw : TermRun.Word} (hc : q.c0 = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw) :
    q.a = .var "z" ∧ q.τ = .int ∧ q.ws = [TermRun.cst (.num 0)] := by
  obtain ⟨_, ht⟩ := hq.term
  rw [hc, Spike.Lib.HelloMainPreSrc.c0H_term] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := hq.ev
  rw [hc, ← ha'] at hev
  change TermRun.lookupE (Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw).env "z" = _ at hev
  rw [Spike.Lib.HelloMainPreSrc.c0H_z] at hev
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hev)
  exact ⟨ha'.symm, h1.symm, h2.symm⟩

/-- **`hbox` at `c0H`'s controls** (`MainWcPS.hbox`): the box's value is one `int` word represented by `0`. -/
theorem hbox_L1 {ms : Spike.Lib.MemSide isaLSE2} {lab : Label → Int64} {lbl' : WeakMem.AllocLabel → Option Nat}
    {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hJ : ∀ σ c, Jr1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw) :
    ∀ q : AGB ms lab, (∃ σ, Jr1 σ q.1.c0) → BoxW lbl' q.1 := by
  rintro q ⟨σ, h⟩
  obtain ⟨w0, w1, w2, mw, hc⟩ := hJ σ _ h
  obtain ⟨-, ht, hw⟩ := box_c0H q.2 hc
  exact ⟨_, hw, by rw [ht]; rfl, ⟨by decide, rfl⟩⟩

/-- **`hcell0` at `c0H`'s controls** (`MainWcPS.hcell0`, `StartGlue.hcellB_of_wordsNone`): a box's fitting cell
(`int`: two units, the word one header past the cell) is mapped and shared (`StartH0.mp_cellH`) and unloaded under
the start's `FS` (`WordsNone`). -/
theorem hcell0_L1 {lab : Label → Int64} {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hJ : ∀ σ c, Jr1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw) :
    ∀ q : AGB (MS) lab, (∃ σ, Jr1 σ q.1.c0) → ∀ o' : Nat,
      (MS).lo o' → o' + (MS).units 1 q.1.τ ≤ (MS).cells →
      (MS).mp ⟨BitVec.ofNat 64 ((MS).heap + 16 * o' + (MS).off 1 q.1.τ), 8⟩ true ∧
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m →
        Mem.loadInt m.dmem (BitVec.ofNat 64 ((MS).heap + 16 * o' + (MS).off 1 q.1.τ)) 8 = none := by
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hhb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = 4194304 := rfl
  have hu2 : (MS).units 1 .int = 2 := rfl
  have hf2 : (MS).off 1 .int = 8 := rfl
  refine Spike.Lib.A64.WakePh.StartGlue.hcellB_of_wordsNone (fun _ h => h.1.wn) (Nat.le_of_eq hh.symm)
    (by rw [hh, hcl, ← hA]; omega) (by rw [hh, hcl]; omega) (P := fun q => ∃ σ, Jr1 σ q.c0) ?_
    (fun q hq o' _ ho => ?_)
  · rintro q ⟨σ, h⟩
    obtain ⟨w0, w1, w2, mw, hc⟩ := hJ σ _ h
    rw [(box_c0H q.2 hc).2.1, hu2, hf2]; omega
  obtain ⟨σ, h⟩ := hq
  obtain ⟨w0, w1, w2, mw, hc⟩ := hJ σ _ h
  have ht := (box_c0H q.2 hc).2.1
  rw [ht, hu2] at ho
  rw [ht, hf2]
  refine Spike.Lib.A64.HelloPh.StartH0.mp_heapH hpw i fun k hk => ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Scc.Sem.Range.contains; omega

end Spike.Lib.A64.HelloPh.MainWcL1Q

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Q.rtWords_offArW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Q.rtWords_offArW

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Q.rtFree_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Q.rtFree_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Q.hlim_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Q.hlim_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Q.box_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Q.box_c0H

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Q.hbox_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Q.hbox_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Q.hcell0_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Q.hcell0_L1
