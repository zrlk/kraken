/-
**hello.w's root: the memory side's and the arena's premises of `HrdS.hrd_WSHF` at `msUH`** (AArch64;
the twins of the arena cases of `WcWfR.hTopP_Rpl` for wake's `wc_main`, here at `wc_rodata`'s
buffer call and the root's memory sides `StartH0U.msUH` at any frames).

At `msUH … fs` (`msOfA` at the arena `arW`, the start's frame condition `MainGlue.FS` with its `WordsNoneP`):
- `hctr_U`, `hheap_U`, `hoff_U`, `hnew_U`: the memory side's arena is `arW`'s (`rfl`);
- `hlt_U`, `h64_U`: the counter word below the heap and below `2 ^ 64` (A8; `Land.hlt_R`'s argument);
- `hpool_U`: the stack pool's base in the address space;
- `hmp_U`: a location the memory side lets the thread write is mapped writable;
- `hmem_U`: the counter word and every header word are unloaded under `FS` (`WordsNone`, `hmem_of_wordsNone`);
- `hno_U`: neither is owned at any phase of `ownH` (the owned words off the arena: `WcWfR.not_ownW`,
  `StartH0Ti.offW_arW`, `CalWf.hoffN_W`);
- `hX0a_U`: the allocator's nodes are at free pcs, so in `X0WH` (`WcWfR.allocW_freeH`,
  `StartGlue.x0WH_of_freeNH`).

`hrd_WSHF`'s `hctx` (the counter add inside the root's `Ctx`) is not here: `Ctx` is the root's choice
(`HelloRootO.helloDR`'s), which has no hello instance yet (`Land3`'s note).
-/
import Spike.Lib.A64HelloStartH0U
import Spike.Lib.A64HelloHrdS
import Spike.Lib.A64HelloWcWfR
import Spike.Lib.A64WakeWcWfR
import Spike.Lib.A64HelloStartGlue
import Spike.Lib.A64WordsNone

namespace Spike.Lib.A64.HelloPh.HrdArena

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.WakeLoadT (L0T ls0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
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
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The root's memory side at the frames `fs`. -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls fs

section Arena

variable {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
  {fs : List TermRun.Frame}

/-- `hrd_WSHF`'s `hctr`. -/
theorem hctr_U : (MSU).ctr = (AR).ctr := rfl

/-- `hrd_WSHF`'s `hheap`. -/
theorem hheap_U : (MSU).heap = (AR).heap := rfl

/-- `hrd_WSHF`'s `hoff`. -/
theorem hoff_U : ∀ k τ, (MSU).off k τ = (AR).off k τ := fun _ _ => rfl

/-- `hrd_WSHF`'s `hnew`. -/
theorem hnew_U : (MSU).newOk → (AR).newOk := id

/-- **`hrd_WSHF`'s `hlt`**: the counter word lies below the arena, in `.data` below the heap (A8). -/
theorem hlt_U (hc : Spike.Lib.A64.Rt.CtrZ o) : (AR).ctr + 8 ≤ (AR).heap := by
  have hpl := Spike.Lib.PlaceW.link IH hpw
  obtain ⟨-, h2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW hpl hc
  have hh := Spike.Lib.A64.Rt.ArenaW.PlaceW.heapOk_of_placeW hpl
  simp only [Scc.Cert.PlaceOK.A64.heapOk, Bool.and_eq_true] at hh
  have hb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ (Ly).Λ.heap.lo :=
    Scc.Cert.PlaceOK.dataBelow_of_dataBelowHeap hh.2
  have h2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := h2
  show Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.heap.lo
  omega

/-- **`hrd_WSHF`'s `h64`**: the counter word below `2 ^ 64` (in `.data`, below `2 ^ 32`). -/
theorem h64_U (hc : Spike.Lib.A64.Rt.CtrZ o) : (AR).ctr < 2 ^ 64 := by
  have hpl := Spike.Lib.PlaceW.link IH hpw
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW hpl
  obtain ⟨-, h2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW hpl hc
  have h2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := h2
  show Scc.Cert.PlaceOK.heapUseOf (Ly).Λ < 2 ^ 64
  omega

/-- **`hrd_WSHF`'s `hpool`**: the stack pool's base is in the address space. -/
theorem hpool_U : (Ly).Λ.stackPool.lo ≤ 2 ^ 64 := by
  have := (Ly).pool_fit
  omega

/-- **`hrd_WSHF`'s `hmp`**: a location the memory side lets the thread write is mapped writable. -/
theorem hmp_U : ∀ l, (MSU).mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true l = true :=
  fun _ h => h.1

/-- The arena's offset is at most its units' room at every call (one element: `arOf_off_eq`,
`arOf_units_pos`). -/
theorem hoffQ_U : ∀ q : Call, q.OK (MSU) (Ly).lab → (MSU).off q.n q.τ ≤ 16 * (MSU).units q.n q.τ := by
  intro q hq
  have hu := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) (n := q.n) hq.accs
  have hf := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) (n := q.n) hq.accs
  show (Spike.Lib.A64.Rt.arOf (Ly).Λ).off q.n q.τ ≤ 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).units q.n q.τ
  rw [hf]; omega

/-- **`hrd_WSHF`'s `hmem`** at the start's frame condition `FS`: the counter word and every header word are
unloaded (`WordsNone`, the arena inside `.heap`, the counter inside `.data`). -/
theorem hmem_U (hc : Spike.Lib.A64.Rt.CtrZ o) {k0 v : BitVec 64} :
    ∀ q : Call, q.OK (MSU) (Ly).lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 (MSU).ctr ∨ ∃ o', o' + (MSU).units q.n q.τ ≤ (MSU).cells ∧ w.toNat = q.hdrAt (MSU) o') →
      ∀ m, FS (Ly) (RS) helloLsw k0 v m → Mem.loadInt m.dmem w 8 = none := by
  have hpl := Spike.Lib.PlaceW.link IH hpw
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceW.wf_link_of_placeW IH hpw
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW hpl hc
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW hpl
  have hh : (MSU).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MSU).cells = Scc.Cert.PlaceOK.allocCells := rfl
  have hct : (MSU).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  exact Spike.Lib.A64.Alloc.hmem_of_wordsNone hwf (fun m h => h.1.wn) (by rw [hh]; exact Nat.le_refl _)
    (by rw [hh, hcl]; omega) (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩)
    (hoffQ_U hpw i0)

/-- **The owned words are off `arW`'s cells and its counter** (`WcWfR.offW_own` at `IH`): the four counters
(`StartH0Ti.offW_arW`) and `scc_rt_nthreads` (`CalWf.hoffN_W`). -/
theorem offH_own (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w', (w' = (Ly).pnA ∨ w' = (Ly).lockA ∨ w' = (Ly).freeNA ∨ w' = (Ly).nextA ∨ w' = NT) →
      ¬ ((AR).heap ≤ w'.toNat ∧ w'.toNat < (AR).heap + 16 * (AR).cells) ∧ w' ≠ BitVec.ofNat 64 (AR).ctr :=
  fun w' hw' => by
    have hof : ¬ ((AR).heap ≤ w'.toNat ∧ w'.toNat < (AR).heap + 16 * (AR).cells) ∧
        (⟨w', 8⟩ : Loc) ≠ (AR).ctrLoc := by
      rcases hw' with rfl | rfl | rfl | rfl | rfl
      · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hpw IH _ (Ly).pn_mem
      · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hpw IH _ (Ly).lock_mem
      · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hpw IH _ (Ly).freeN_mem
      · exact Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hpw IH _ (Ly).next_mem
      · exact Spike.Lib.A64.WakePh.CalWf.hoffN_W hpw IH hA13
    exact ⟨hof.1, fun h => hof.2 (by rw [h]; rfl)⟩

/-- **`hrd_WSHF`'s `hno`**: the counter word and every header word are owned at no phase of `ownH`. -/
theorem hno_U (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ q : Call, q.OK (MSU) (Ly).lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 (MSU).ctr ∨ ∃ o', o' + (MSU).units q.n q.τ ≤ (MSU).cells ∧ w.toNat = q.hdrAt (MSU) o') →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.A64.HelloPh.ownH (Ly) NT j := by
  intro q hq w hw
  refine Spike.Lib.A64.WakePh.WcWfR.not_ownW (heap := (MSU).heap) (cells := (MSU).cells) (ctr := (MSU).ctr)
    (offH_own hpw i0 hA13) ?_
  rcases hw with h | ⟨o', ho, h⟩
  · exact .inl h
  · refine .inr ?_
    have h1 := hoffQ_U hpw i0 q hq
    have hroom := hq.room
    rw [hq.off] at h1
    rw [Spike.Lib.A64.Alloc.Call.hdrAt] at h
    generalize q.n * (Spike.Lib.A64.Alloc.mOf q.h).toNat = k at h1 h
    omega

end Arena

section X0

variable {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
  {fs : List TermRun.Frame}

/-- **`hrd_WSHF`'s `hX0a`**: the allocator's nodes are at free pcs (`WcWfR.allocW_freeH`), so in `X0WH` at the
take site (`StartGlue.x0WH_of_freeNH`), at any region and frame condition. -/
theorem hX0a_U (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hlo0 : Λ0.code.lo = lo)
    {R : Spike.Lib.Region} {F : MachineData → Prop} :
    ∀ q : Call, AllocW (MSU) q (fun s _ => X0WH (Ly) (AX) s) (fun _ _ => False) (Ly).exe (Ly).endPc R F := by
  have ho : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw IH l x (by
      show codeOf Λ0.code.lo o.prog l = some x
      rw [hlo0, ho]; exact h)
  have hX0 := Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  intro q
  exact Spike.Lib.A64.AllocG.AllocW.imp (Spike.Lib.A64.HelloPh.WcWfR.allocW_freeH hlab)
    (Spike.Lib.A64.Alloc.AllocW.triv _ _) (fun s _ h _ => hX0 s h)

end X0

end Spike.Lib.A64.HelloPh.HrdArena

/-- info: 'Spike.Lib.A64.HelloPh.HrdArena.hmem_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdArena.hmem_U

/-- info: 'Spike.Lib.A64.HelloPh.HrdArena.hno_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdArena.hno_U

/-- info: 'Spike.Lib.A64.HelloPh.HrdArena.hX0a_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdArena.hX0a_U
